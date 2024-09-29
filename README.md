# XStar
Build an integrated, programmable program verifier for X. Take the C language as an example.

## Overview

Verified software projects are usually conducted by two groups of people: _program developers_ and _proof developers_. The typical workflow is as follows:

1. Program developers write the implementation code in C.

    Program developers should have a clear understanding of the program's functionality (i.e., what the program does) and why the program works (i.e., the intuitive reasoning process).

2. Program developers provide additional specifications and reasoning hints in the form of comments and documentation.

    These natural language specifications and hints can be scattered throughout the codebase and may become out of sync with the code. Additionally, there are no clear guidelines for program developers on how to express their ideas.

3. Proof developers embed the implementation C code into a program verifier, understanding and translating the specifications provided by the program developers into the program verifier's specification language. They then complete the proof, possibly with the help of hints from program developers.

    The specification translation process is error-prone and time-consuming. The embedding process can be automated, but the environment gap between the proof developers and the program developers can still hinder the proof process.

How CStar changes the workflow:

1. Program developers write a single CStar source file, which contains the implementation C code together with ghost C code (in C23 attributes). The ghost code describes the program's functionality using definitions in the familiar C language and the reasoning process and additional proof hints in an operational style (using ghost C commands and declarations).

    This code should be easily written by programmers without formal verification background. It can first be executed to test the conformance of implementation code with the added ghost functional behavior assertions.

2. To the static verification phase, the implementation code and the ghost code are extracted by the CStar extractor, producing logical datatype, function, and predicate definitions in Higher-order Logic (HOL), together with a Separation Logic assertion-annotated C code for symbolic execution.

    This way, programmers can use their familiar C language to write the program and the proof hints while communicating their ideas to the proof developers by extracting these definitions and hints into a verifiable form.

3. The proof developers can use the extracted definitions and hints to complete the proof in a programmable proof development environment.

    The extracted output can be directly used by the proof developers; they can complete the proof in a C programmable proof development environment (thanks to the LCF-style proof support).

## Getting Started
