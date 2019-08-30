This directory contains the examples from the Software Foundations series 
available at: https://softwarefoundations.cis.upenn.edu

You can use Stainless to verify the safety properties of all the programs:

    stainless-scalac sf1-logical-foundations/*.scala

To check for termination of all of your programs:

    stainless-scalac sf1-logical-foundations/*.scala --termination

To compile all the files with scalac:

    scalac sf1-logical-foundations/*.scala -d /anyfolder/for/classfiles $(find /path/to/stainless/frontends/library/ -name "*.scala")

After compilation, you can run a particular file (e.g. with Basics) with:

    scala -cp /anyfolder/for/classfiles sf1.Basics
