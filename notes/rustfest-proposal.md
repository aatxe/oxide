# Proposal for RustFest Paris

## Metadata

__Title__: What's the meaning of Rust types?  
__Session Format__: Standard Talk (30mn)  
__Tags__: Scientific, Lecture, Theory  

## Abstract

As Rust programmers, we all have an intuitive sense that types are useful, and of course, we rely on
Rust's ownership model and borrow checker to keep our programs free of data races. But what exactly
do our types _mean_? In this talk, we'll explore an ongoing effort to build an accessible formal
semantics for Rust and its application to understanding the meaning of types in Rust programs.
Further, we'll use this newfound understanding of types to explore interesting ways of enforcing
correctness and security criteria through types.

[A concise, engaging description for the public program. Limited to 600 characters.]

## Details

### Rough Outline

1. Wirlwind Introduction to Semantics
    1. What are PL semantics?
        - Semantics are formal ways of understanding the meaning of elements of our programming
          languages
        - Without semantics, we just have a pile of uninterpretable symbols
        - Real languages get around this often by having ad-hoc meaning defined in interpreters,
          compilers, and/or informal specifications
    2. How do we describe them?
        - Denotationally -- by giving an interpretation of our language as mathematical objects
        - Operationally -- by giving rules that describe steps in an interpreter
    3. Why should we care?
        - Extensibility -- formal semantics can give us a basis for designing language extensions,
          which could prove useful in writing RFCs
        - Reasoning -- semantics can be used to build a more complete intuition about a language,
          which can prove useful while programming
2. Parametricty and Rust
    1. Featherweight Rust
        - Compile Rust to a bit more explicit form (to make our semantics compositional)
        - Ownership codified using fractional permissions
    2. Expressive Layers of (formal) Rust
        - Rust0 -- safe Rust without any standard library stuff
        - Rust1 -- extend Rust0 with `Box<T>` and `Vec<T>`, providing access to the heap
        - Rust2 -- extend Rust1 with `Rc<T>` and `Arc<T>`, giving more capacity to share
        - Rust3 -- extend Rust2 with `Cell<T>` and `RefCell<T>`, producing "interior mutability"
    3. What is parametricity?
        - Parametricity is a kind of "abstraction" result telling you that abstractions _are_
          abstractions
        - A polymorphic function is parametric if it acts the same for all types.
        - A language is parametric if all polymorphic functions are parametric.
    4. Parametricity in Rust
        - Our formal Rust model is parametric!
        - Real Rust is close to parametric, though trait specialization breaks it.
        - Depending on the precise details of specialization, we may be able to know from a type if
          specialization is possible. So, all hope is not lost!
3. Theorems for Free!
    1. "Identity" Functions (`fn<T>(T) -> T`)
        - Functions at this type must return their argument, panic/abort, or otherwise diverge.
        - Effects during the function _cannot_ depend on the value of the argument.
        - Our identity function behaves like identity, i.e. it composes transparently with all total
          functions of the form `fn(A) -> B` where `A` and `B` are concrete types.
    2. Noninterference
        - Noninterference is a security property that states that public outputs of programs do not
          depend on the private inputs.
        - Can model interference via parametricity!
        - Define a `Secret<T>` type and only give it functions that return `Secret<U>` results.
        - Type system now prevents secret values from flowing out!
    3. Cryptographic Nonces
        - Ownership lets us track "use" of values, which is not possible in other parametric
          languages. This gives us more free theorems!
        - Define a `Nonce` type that keeps its internal value opaque, ensure that functions that use
          it always take ownership up of it.
        - Type system not enforces that the nonce is only ever used once.
        - Possible extension: if you want to do sequential nonces, you can have a provider that will
          always yield a new sequential `Nonce` that, again, will be moved into any function.
    4. Relaxed Noninterference
        - Relaxed noninterference by using trait bounds on secret types as _declassification
          policies_. These bounds will be for types that yield _non_-secret values.
        - We lose noninterference proper, but gain a reasoned method of managing security policies
          of functions via our types.

### Desired Outcome

This talk seeks to help transfer knowledge and interest in programming language theory to the
broader Rust community while helping to build a more thorough understanding of types that could help
when programming.

### Intended Audience

The intended audience of this talk is at least intermediate Rust programmers who have some interest
in the formal world of programming languages and type theory. We won't assume any _pre-existing_
knowledge of type theory, and the goal is really to require just general mathematical competency
(i.e. algebra).

[Include any pertinent details such as outlines, outcomes or intended audience.]

## Pitch

[Explain why this talk should be considered and what makes you qualified to speak on the topic.]

## Bio

Aaron Weiss is a PhD student at Northeastern University working with Prof. Amal Ahmed at the
intersection of programming languages and security. As part of his research, Aaron is producing a
source Rust-like formal model for use in designing new extensions and use cases for Rust.

[Your bio should be short, no longer than 500 characters. It's related to why you're speaking about
this topic.]
