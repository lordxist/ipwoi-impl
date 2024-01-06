# Implementation of "Internal parametricity, without an interval"

First approach to a Haskell implementation of the local theory of ["Internal parametricity, without an interval" (Altenkirch et al. 2024)](https://arxiv.org/abs/2307.06448) (arXiv preprint).

Work in progress. Currently able to typecheck the polymorphic identity function parametricity (cf. sec. 2.2 of the paper): defined in `Main.hs` in `idFctParametricityTm` (and its type `idFctParametricity`).

Usage:
```
$ ghc Main.hs
$ ./Main -s
Term: StarTm
Type: One
_________________________________
1 ↠ 1
_________________________________
★ : 1 ✓
★ ↠ ★
```

First result line gives the normalized type. Then follows whether the term checks against the type or not. If yes, the last line gives the normalized term.

Instead of `StarTm`, `One`, provide terms and types you want to typecheck, in the form that Haskell `read` expects (i.e., `show` the types/terms specified in `Main.hs`); `idFctParametricityTm` (and its type `idFctParametricity`) are available as shorthands:

```
Term: idFctParametricityTm
Type: idFctParametricity  
_________________________________
∏∏∑U.El(0).El(π₁ 0).∏2.∏D(0).D(app⟨∑U.El(0).El(π₁⟨U.El(0)⟩ 0)⟩(2, ⟨U.El(0)⟩(c 2, 1))) ↠ ∏∏∑U.El(0).El(π₁ 0).∏2.∏D(0).D(app⟨∑U.El(0).El(π₁⟨U.El(0)⟩ 0)⟩(2, ⟨U.El(0)⟩(c 2, 1)))
_________________________________
\{\{\{π₂ apd(∑U.El(0).app(3, 0):El(π₁ 0))(⟨∀U.∀d(U.El(0))(0)⟩(unspan(2, ∑2.D(0).π₁ 0), ⟨2.D(0)⟩(1, 0)))}}} : ∏∏∑U.El(0).El(π₁ 0).∏2.∏D(0).D(app⟨∑U.El(0).El(π₁⟨U.El(0)⟩ 0)⟩(2, ⟨U.El(0)⟩(c 2, 1))) ✓
\{\{\{π₂ apd(∑U.El(0).app(3, 0):El(π₁ 0))(⟨∀U.∀d(U.El(0))(0)⟩(unspan(2, ∑2.D(0).π₁ 0), ⟨2.D(0)⟩(1, 0)))}}} ↠ \{\{\{π₂ apd(∑U.El(0).app(3, 0):El(π₁ 0))(⟨∀U.∀d(U.El(0))(0)⟩(unspan(2, ∑2.D(0).π₁ 0), ⟨2.D(0)⟩(1, 0)))}}}
```

The `-s` argument is optional and simplifies the pretty printing (i.e., omits most type ascriptions).
