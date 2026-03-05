# Contributing to Stainless

## Stainless cheat sheet

### Debug Stainless (JVM)

---

```bash
sbt -jvm-debug <port>
```

---

### VS Code / Metals Debug Attach

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "scala",
      "request": "attach",
      "name": "Scala-attach-5005",
      "buildTarget": "root",
      "hostName": "localhost",
      "port": 5005
    }
  ]
}
```

---

### Print Scala Compiler Trees

```bash
scala -Vprint:posttyper File.scala
```

---

### Run Stainless from sbt (Development)

```bash
sbt
stainless-dotty / run /absolute/path/to/file.scala
```

---

### Run Integration Tests single suite

Example for `stainless.DottyExtractionSuite`

```bash
sbt -batch \
  -Dtestsuite-parallelism=3 \
  -Dtestcase-parallelism=5 \
  "stainless-dotty / IntegrationTest / testOnly stainless.DottyExtractionSuite"
```

---

### Run Main of a Stainless project with sbt plugin

This command is used to run the main class of a project verified with stainless when using the stainless sbt plugin.

```bash
runMain your.package.Main
```

---

### Build Stainless sbt Plugin

Run this script to build the sbt plugin

```bash
./bin/package-sbt-plugin.sh
```

---

### Scala → JVM Bytecode Inspection

```bash
scalac File.scala
javap -c -l -private *.class
```

---

### Print Dotty Trees that stainless receives

```bash
scalac -Xprint:typer File.scala
```

---

### Run Stainless with Explicit JVM Options

```bash
sbt -J-Xmx8G stainless-dotty / run /absolute/path/to/file.scala
```