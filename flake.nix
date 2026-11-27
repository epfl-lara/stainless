# Development environment for Stainless, matching the toolchain of the CI.
#
#   nix develop                      # enter the shell
#   sbt Universal/stage              # build frontends/dotty/target/universal/stage/bin/stainless-dotty
#   sbt test IntegrationTest/test    # run the test suites, as ./stainless-ci.sh does
#
# The versions are pinned to the ones of the CI, and must be kept in sync with:
#   - JDK:     .github/workflows/stainless-CI.yml (Temurin, `java-version`)
#   - sbt:     project/build.properties
#   - solvers: stainless-ci.sh (`--install-solvers`)
# The solvers are the upstream release binaries that the CI downloads, patched to run on NixOS.
{
  description = "Stainless development environment, with the JDK, sbt and solvers of the CI";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      # The release binaries of the solvers that the CI uses exist for x86_64 Linux only.
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      inherit (pkgs) lib fetchurl stdenv;

      # Temurin, as resolved by `actions/setup-java` for `java-version: 25`.
      jdkVersion = "25.0.5.1+2";
      jdk = pkgs.temurin-bin-25.overrideAttrs (old: {
        version = jdkVersion;
        srcs = [
          (fetchurl {
            url = "https://github.com/adoptium/temurin25-binaries/releases/download/jdk-25.0.5.1%2B2/OpenJDK25U-jdk_x64_linux_hotspot_25.0.5.1_2.tar.gz";
            hash = "sha256-dg+Rsiw+/JvRtk/5UFmCMb6CkozIB+MGkaDnoplaYsA=";
          })
          (fetchurl {
            url = "https://github.com/adoptium/temurin25-binaries/releases/download/jdk-25.0.5.1%2B2/OpenJDK25U-jmods_x64_linux_hotspot_25.0.5.1_2.tar.gz";
            hash = "sha256-3D3bLevt1XFHNiKnfoR9xmJ5WecDHwqP8XrYi49PfyA=";
          })
        ];
      });

      # The sbt launcher, which then fetches the sbt version of project/build.properties.
      sbt = stdenv.mkDerivation rec {
        pname = "sbt";
        version = "1.12.4";
        src = fetchurl {
          url = "https://github.com/sbt/sbt/releases/download/v${version}/sbt-${version}.tgz";
          hash = "sha256-OgLUzZhn/OJZgvmxaMJF/05HjddpQV21QuW+65+fuHo=";
        };
        nativeBuildInputs = [ pkgs.makeWrapper ];
        installPhase = ''
          mkdir -p $out/share/sbt $out/bin
          cp -r bin conf $out/share/sbt/
          rm $out/share/sbt/bin/sbtn-* $out/share/sbt/bin/sbt.bat
          patchShebangs $out/share/sbt/bin/sbt
          makeWrapper $out/share/sbt/bin/sbt $out/bin/sbt --set-default JAVA_HOME ${jdk}
        '';
      };

      # A solver binary out of an upstream release, patched to run on NixOS.
      solver = { pname, version, src, binary, unpack ? true }:
        stdenv.mkDerivation {
          inherit pname version src;
          nativeBuildInputs = [ pkgs.autoPatchelfHook ] ++ lib.optional unpack pkgs.unzip;
          buildInputs = [ (lib.getLib stdenv.cc.cc) ];
          dontUnpack = !unpack;
          sourceRoot = ".";
          dontStrip = true;
          installPhase = ''
            install -Dm755 ${binary} $out/bin/${pname}
          '';
        };

      z3 = solver rec {
        pname = "z3";
        version = "5.4.1";
        src = fetchurl {
          url = "https://github.com/Z3Prover/z3/releases/download/z3-${version}/z3-${version}-x64-glibc-2.39.zip";
          hash = "sha256-tUi6xI7yRStOCeopRc9LAR1fQ/zznkeZ3yaO5+B2nYU=";
        };
        binary = "z3-${version}-x64-glibc-2.39/bin/z3";
      };

      cvc5 = solver rec {
        pname = "cvc5";
        version = "1.4.2";
        src = fetchurl {
          url = "https://github.com/cvc5/cvc5/releases/download/cvc5-${version}/cvc5-Linux-x86_64-static.zip";
          hash = "sha256-frGPjIFMNqRsWn0AOYPpz7xLCpgo1t1ZYjkpG9TMYdg=";
        };
        binary = "cvc5-Linux-x86_64-static/bin/cvc5";
      };

      cvc4 = solver rec {
        pname = "cvc4";
        version = "1.8";
        src = fetchurl {
          url = "https://github.com/CVC4/CVC4-archived/releases/download/${version}/cvc4-${version}-x86_64-linux-opt";
          hash = "sha256-04p5z5hFknhe2kHsiI2UyhB6wfEwWHQCOAQeKMhHLlE=";
        };
        binary = "$src";
        unpack = false;
      };
    in
    {
      packages.${system} = { inherit jdk sbt z3 cvc5 cvc4; };

      devShells.${system}.default = pkgs.mkShell {
        packages = [ jdk sbt z3 cvc5 cvc4 pkgs.git pkgs.wget pkgs.unzip ];

        JAVA_HOME = "${jdk}";

        # The native Z3 interface (ScalaZ3) extracts the Z3 libraries out of its jar and loads them
        # into the JVM, they need libstdc++.
        LD_LIBRARY_PATH = lib.makeLibraryPath [ (lib.getLib stdenv.cc.cc) ];

        # The Java options of the CI (.github/workflows/stainless-CI.yml), unless already set.
        shellHook = ''
          # Without a UTF-8 locale, the JVM cannot write the class files with non-ASCII names (of
          # shapeless, for instance), and the compilation fails. C.UTF-8 is built into glibc.
          if [ -z "''${LC_ALL-}''${LC_CTYPE-}''${LANG-}" ]; then
            export LANG=C.UTF-8
          fi
          if [ -z "''${JAVA_OPTS-}" ]; then
            export JAVA_OPTS="-Dsbt.io.implicit.relative.glob.conversion=allow -Xss512M -Xms1024M -Xmx12G -XX:MaxMetaspaceSize=2G -XX:+UseCodeCacheFlushing -XX:ReservedCodeCacheSize=768M -XX:+UseCompactObjectHeaders"
          fi
        '';
      };
    };
}
