# Why do we have ordinary and move closures?

This note exists because I discussed this with Amal, and we will likely want to reproduce some of
this information in the paper.

## Ordinary closures are a special case.

Ordinary closures are a special case of move closures because we can imagine introducing let
bindings for every variable in advance of the closure declaration that bind each variable to its
borrow and then move the borrow. This gives us some indication that perhaps our model would be
simpler if we just included one (especially given it leads to some rule duplication).

## The desugaring is harder than the second set of rules.

Honestly, I think the closure rules are some of the simpler rules in `oxide`. By contrast, the two
desugarings I can imagine are non-trivial. One involves adding a binding for _every_ variable in
context which then need to end after the closure definition. This feels bad because we don't need
to capture probably the bulk of the variables in the context. The alternative is to compute the set
of referenced variables in the closure body first and then add the bindings. My impression is that
this process is not macro-expressible, and thus, should be considered complex. By contrast, the
extra rules for ordinary closures don't seem to make the proofs nor the comprehension of our
semantics any harder.
