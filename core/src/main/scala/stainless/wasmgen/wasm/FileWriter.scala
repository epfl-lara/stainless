/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.wasmgen.wasm

import java.io.{IOException, File, FileWriter => JFW}
import scala.sys.process._
import inox.Context

class FileWriter(module: Module, context: Context) {
  private val outDirName = "wasmout"
  private def withExt(ext: String) = s"$outDirName/${module.name}.$ext"

  private object Env {
    trait OS
    object Linux extends OS
    object Windows extends OS
    object Mac extends OS

    lazy val os = {
      // If all fails returns Linux
      val optOsName = Option(System.getProperty("os.name"))
      optOsName.map(_.toLowerCase()).map { osName =>
        if (osName contains "linux") Linux
        else if (osName contains "win") Windows
        else if (osName contains "mac") Mac
        else Linux
      } getOrElse Linux
    }
  }

  private def writeWasmText(fileName: String): Unit = {
    val fw = new JFW(new File(fileName))
    fw.write(Printer(module))
    fw.flush()
    fw.close()
    context.reporter.info(s"WebAssembly text file $fileName was generated.")
  }

  private def writeWasmBinary(fileName: String, textFile: String): Unit = {
    val w2wOptions = s"$textFile -o $fileName"
    val wat2wasm = {
      import Env._
      os match {
        case Windows => "wat2wasm.exe"
        case _ => "wat2wasm"
      }
    }
    try {
      s"$wat2wasm $w2wOptions".!!
      context.reporter.info(s"WebAssembly binary file $fileName was generated.")
    } catch {
      case _: IOException =>
        context.reporter.error(
          "wat2wasm utility was not found in system path, " +
          "or did not have permission to execute. " +
          "Skipping creation of wasm binary..."
        )
      case e: RuntimeException =>
        context.reporter.internalError(
          s"wat2wasm failed to translate WebAssembly text file ${withExt("wat")} to binary"
        )
    }
  }

  private def writeNodejsWrapper(fileName: String, moduleFile: String): Unit = {
    val wrapperString =
      s"""|// `Wasm` does **not** understand node buffers, but thankfully a node buffer
          |// is easy to convert to a native Uint8Array.
          |function toUint8Array(buf) {
          |  var u = new Uint8Array(buf.length);
          |  for (var i = 0; i < buf.length; ++i) {
          |    u[i] = buf[i];
          |  }
          |  return u;
          |}
          |// Loads a WebAssembly dynamic library, returns a promise.
          |// imports is an optional imports object
          |function loadWebAssembly(filename, imports) {
          |  // Fetch the file and compile it
          |  const buffer = toUint8Array(require('fs').readFileSync(filename))
          |  return WebAssembly.compile(buffer).then(module => {
          |    return new WebAssembly.Instance(module, imports)
          |  })
          |}
          |
          |var memory = new WebAssembly.Memory({initial:1});
          |var importObject = {
          |  system: {
          |    mem: memory,
          |
          |    // Reads a string from linear memory and prints it to the console
          |    printString: function(arg) {
          |      var bufView = new Uint8Array(memory.buffer);
          |      // Reconstruct 32-bit integer length from 4 first bytes in little endian
          |      var len = (
          |        bufView[arg] +
          |        bufView[arg+1] * 0x100 +
          |        bufView[arg+2] * 0x10000 +
          |        bufView[arg+3] * 0x1000000
          |      );
          |      var i = 0;
          |      var result = "";
          |      while(i < len) {
          |        result += String.fromCharCode(bufView[arg+i+4]);
          |        i = i + 1
          |      }
          |      console.log(result);
          |    }
          |
          |  }
          |};
          |
          |loadWebAssembly('$moduleFile', importObject).then(function(instance) {
          |  instance.exports._main_()
          |}).catch( function(error) {
          |  console.log("Error in wasm application: " + error)
          |  process.exit(1)
          |})
          |""".stripMargin
    val fw = new JFW(new File(fileName))
    fw.write(wrapperString)
    fw.flush()
    fw.close()
    context.reporter.info(s"Javascript wrapper file $fileName was generated.")
  }

  def writeFiles(): Unit = {
    val outDir = new File(outDirName)
    if (!outDir.exists()) {
      outDir.mkdir()
    }
    writeWasmText(withExt("wat"))
    writeWasmBinary(withExt("wasm"), withExt("wat"))
    writeNodejsWrapper(withExt("js"), withExt("wasm"))
  }

}
