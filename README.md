# A Directed, Topos-Theoretic Type Theory

In this research project, I design and implement a type system that displays aspects of modal and directed type theories, at no more theoretical complexity cost than Martin Löf type theory.

For the theory, see [theory/theory.pdf](theory/theory.pdf).

As this is a research project, no thought has been put toward efficiency of implementation, only towards design, simplicity, and correctness.

## Compilation

The implementation is written in a mixture of Agda and Haskell. I am using the following versions; I have not tested others.

- Agda 2.6.3
    - agda-stdlib-2.0-dev-2023-05-04
- Haskell 9.4.8
    - base 4.17.2.1
    - transformers 0.5.6.2

To compile; run `sh build.sh`. The resulting binary will be called `Main`, and placed in the toplevel directory.

## Syntax

- Variables can consist of any string of alphanumeric characters, not starting in `λ` or `Π`.

- Terms can consist of:
    - Variables.
    - The universe, `★` (u+2605)
    - An element `<A>` of type `★`, where `A` is a type.
    - `a[σ]`, where `a` is a term and `σ` is a substitution.
    - Pi types: `Π x :[σ] A → body`
    - Lambdas: `λ x :[σ] A → body`
    - Applications: `f x`
    - `σ.2`, where `σ` is a substitution.

- Types are implicitly coerced from terms of type `★[σ]`, for any substitution `σ`.

- Substitutions can consist of:
    - `id`, the identity substitution.
    - `σ[τ]`, where `σ` and `τ` are substitutions. This implements composition of substitutions, but can also be seen as applying `τ` to each term in `σ`.
    - `σ.1`, where `σ` is a substitution.
    - Comma-delimited lists, possibly beginning in a substitution, with the remaining elements having the form `x : [ σ ] A = a`. If there is no initial substitution, the unique substitution to the empty context is used. The empty string is a valid list.

- `[σ]` binds tightly; For example, `\a:A. body[σ]` means `\a:A. (body[σ])`, not `(\a:A. body)[σ]`.

- Comments are delimited by `--`, and last until the end of the line.

## Eta

The implementation does not support eta-equivalence checking. It does, however, support the commutation of substitutions with eliminators, which I present in the theory as a consequence of eta.
