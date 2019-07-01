# FAQ

The following two interviews are extracted from the [Center For Digital Trust (C4DT) newsletter #2 in April 2019](https://mailchi.mp/6d0f3c2d3070/c4dt-newsletter-april-2366037?e=ec2376a2c8).

## Interview with Prof. Viktor Kunčak

> Prof. Viktor Kunčak leads the EPFL Laboratory for Automated Reasoning and Analysis (LARA), which has developed several tools for automated formal verification and synthesis of software in programs written in the Scala programming language widely used in industry. In this interview we focus on the Stainless library.

### 1. Formal software verification (FSV) versus software testing techniques, such as fuzzing? What are the pros and cons?

**VK:** Formal software verification finds proofs that programs work under all scenarios of interest. FSV tools help developers construct such proofs, automatically searching for proofs using theorem proving and constraint solving (using, e.g. SMT solvers), and static analysis to discover program invariants. When it succeeds, FSV is guaranteed to identify all software errors, including, for example, security vulnerabilities or cases when the computation produces a wrong numerical or symbolic result. Because it involves building proofs, this approach may require knowledge of proofs by induction and substitution of equals for equals, typically covered in computer science undergraduate university education. The best approach to obtain formally verified software is to perform FSV while software is developed. If we try to apply FSV after software is already written, we should be prepared to invest at least the amount of effort needed to rewrite it.

Testing can establish the presence of errors, but not their absence. Basic forms of testing can be easy to deploy, because running a program on a given input is a minimum requirement for software, but such testing is extremely limited. Suppose that we wish to test whether a program running on a smartphone performs multiplication of two machine numbers correctly. If we could check one test per nanosecond, we would need 10^31 billions of years to enumerate all cases. This also illustrates how minuscule of a region of space around a given test a fuzzer can ever explore. Formal software verification can cover all these cases with a single proof because it uses algebraic properties that are independent of the size of the data that software manipulates.

To avoid enumeration, advanced testing methods such as symbolic execution embrace constraint solvers originally developed for formal verification. These techniques reduce to FSV when programs have no loops or recursion; otherwise they end up sampling a small fraction of program executions, so they do not result in a proof. To cover more than just absence of crashes and vulnerabilities, testing also requires insights into the purpose of software, the environment in which the software needs to execute and the expected outputs for given inputs.

### 2. Could give us success stories where other software verification techniques would probably not have solved the challenge?

**VK:** We know of no other method that can establish the level of assurance that formal verification provides. Companies, research labs and research groups have developed proofs of correctness of operating system kernels, brake system for a metro line in Paris, compilers, databases, data structures, smart card wallets, communication protocols, and distributed systems. Yet we are still forced today to fly in airplanes built by companies that lag in the adoption of formal methods.

### 3. How does Stainless differ from other products, for example, from Galois?

**VK:** Stainless is not a commercial product but free software developed through years of our research group's work. It currently works for software in a variant of the Scala programming language (also developed at EPFL). Stainless benefits from a modern strong type system of Scala as well as high-level abstractions for writing code productively. Unlike tools that work with C programs, it leverages memory safety of Scala, avoiding many security issues and low-level crashes. Moreover, it avoids many subtleties of shared mutable objects by focusing on mostly functional programming paradigm. The verification algorithm of Stainless achieves a high degree of automation because it encodes programs and specifications into the constraints understood by SMT solvers (such as Z3, CVC4, and Princess) to find both proofs and errors. Stainless input language integrates specifications into Scala's type system to make specification process a natural extension of writing program types and interfaces.

Stainless supports a fairly general language and a broad class of properties. Related languages and tools include Dafny from Microsoft research and Viper from ETHZ, which employ constraint solvers in a different way, resulting in a different verification experience, but they are also great and general-purpose tools. Other tools focus more on domain- specific languages (such as Cryptol from Galois), which are very effective when the entire problem fits into the particular domain. Tools for other programming languages include Liquid Haskell, KeY tool for Java, or SPARK Ada.

### 4. What are the conditions required for Stainless to be applied to a industry software?

**VK:** It is best to deploy formal verification when starting to develop software. In this way, software and its specifications are developed hand in hand, much like one can define a class hierarchy and other types during the process of writing an object-oriented program. Software that has well-defined modular structure with clear responsibility of different modules is a good candidate for verification because one can expect that specifications at module boundaries will be non-controversial. In terms of developer skills, good knowledge of discrete mathematics, such as proofs by induction and algebra will make developers more effective at verification.

### 5. Much industry software is written in Java. In those cases, can Stainless still be applied?

**VK:** If we had resources, we would like to extend our support for shared mutable state in Scala, which would then make supporting Java mostly a matter of engineering. Whereas functional Scala works as a specification and implementation language, Java is not a good language for specifications, so much that Java verification tools, such as KeY, introduce their own logical notation that developers then must learn.

### 6. Future for FSV and Stainless?

**VK:** We are continuing to build formally specified libraries for Stainless, which will make building formally verified applications easier. We are working on a formally specified actor library for distributed programming, and would like to explore verification of programs using Apache Spark.

We have also developed an approach to generate solidity code from Scala, which we are using to develop formally verified smart contracts. Smart contracts are a great target for verification because their correctness has important financial consequences, and because they are reasonably short, so it is feasible to rewrite them to ensure that they satisfy a formal specification.

