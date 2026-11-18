@echo off

rem Absolute path of the script: https://stackoverflow.com/a/33372703
pushd %~dp0
set script_dir=%CD%
popd

set PATH=%PATH%;"%script_dir%\z3"
set PATH=%PATH%;"%script_dir%\cvc5"

rem --enable-native-access: the native Z3 interface loads Z3 through JNI, which Java 22+ warns about otherwise.
java --enable-native-access=ALL-UNNAMED -jar "%script_dir%\lib\{STAINLESS_JAR_BASENAME}" %*
