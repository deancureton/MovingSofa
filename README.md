# Optimality of Gerver's sofa

This repository contains a Lean 4 proof that Gerver's sofa has the largest area of any shape that can be moved around a right-angled corner in a hallway of width one. This is the moving sofa problem, solved by Jineon Baek in [*Optimality of Gerver's Sofa*](https://arxiv.org/abs/2411.19826) (2024).

```lean
theorem MovingSofa.sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa
```

- The statement is copied from Google DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) and passes [comparator](https://github.com/leanprover/comparator).
- The statement is formalized unconditionally: the Green-type curve area identity and the Minkowski-type mixed area facts that the paper quotes are proved here.
- The proof is about 66,000 lines of Lean, not counting dependencies. It was written in about four days by AI coding agents (OpenAI Codex and Claude Code), directed by Dean Cureton.

## Built on

- **[Jineon Baek's paper](https://arxiv.org/abs/2411.19826)**, which the proof follows step by step.
- **[GerverSofaLean](https://github.com/dawidmtrela-dotcom/GerverSofaLean)** by Dawid Trela: Gerver's four constants exist and are unique, and Gerver's sofa does move around the corner. Vendored in `vendor/gerver-sofa` (v1.1.0, MIT, updated to work with latest mathlib).
- **[formal-conjectures](https://github.com/google-deepmind/formal-conjectures)**, providing the formal statement ([`MovingSofa.lean`](https://github.com/google-deepmind/formal-conjectures/blob/ddfbaf90f4482030d88aae5233fe933874296a23/FormalConjectures/Wikipedia/MovingSofa.lean)).
- **[lean-pool](https://github.com/Vilin97/lean-pool)**: Jonathan Ho's Brunn–Minkowski inequality ([`BrunnMinkowski.lean`](https://github.com/Vilin97/lean-pool/blob/bb74ee07fc23bc81358d75a9c40303e5e27fced8/LeanPool/Isoperimetric/BrunnMinkowski.lean)).
- **[jordan_pick](https://github.com/rkirov/jordan_pick)**: the Jordan curve theorem ([`JordanCurve.lean`](https://github.com/rkirov/jordan_pick/blob/b3c9b7cf7358bf81a077d78ad67e6e8247869ddd/JordanPick/JordanCurve.lean)).
- **[TauCeti](https://github.com/TauCetiProject/TauCeti)**: Jordan curves from two arcs ([`JordanCurve/Path.lean`](https://github.com/TauCetiProject/TauCeti/blob/c52a81811e4626d2e9769fe9b0c701168c211332/TauCeti/Topology/JordanCurve/Path.lean)), the filled hull ([`FilledHull.lean`](https://github.com/TauCetiProject/TauCeti/blob/c52a81811e4626d2e9769fe9b0c701168c211332/TauCeti/Analysis/Normed/Module/FilledHull.lean)), and bounded variation ([`BoundedVariation.lean`](https://github.com/TauCetiProject/TauCeti/blob/c52a81811e4626d2e9769fe9b0c701168c211332/TauCeti/Topology/EMetricSpace/BoundedVariation.lean), [`MetricVariation.lean`](https://github.com/TauCetiProject/TauCeti/blob/c52a81811e4626d2e9769fe9b0c701168c211332/TauCeti/Analysis/Calculus/MetricVariation.lean)).
- **[Mathlib](https://github.com/leanprover-community/mathlib4)**.

## What is proved

A *moving sofa* is a nonempty, closed, connected subset of the horizontal arm of the hallway $(-\infty,1] \times [0,1] \cup [0,1] \times (-\infty,1]$, with a continuous family of rigid motions that starts at the identity, keeps it inside the hallway and ends with it in the vertical arm. `sofaConstant` is the supremum of the areas of moving sofas. The theorem above is Theorem 1.1 of the paper.

Comparator also checks two other theorems. `MovingSofa.GerversSofa.ABφθSpec.existsUnique` says that the four equations defining Gerver's constants $A, B, \varphi, \theta$ have exactly one solution; `gerversSofa` is defined from the solution. `MovingSofa.isMovingSofa_gerversSofa` says that Gerver's sofa is a moving sofa, so the supremum is attained by it.

The statement fixes the initial motion $m_0 = \mathrm{id}$, but the paper allows a translate; the two are proved equivalent. The area of Gerver's sofa is only proved to be at least $11/5$; the value $2.2195\ldots$ is not checked.

## The proof

A sofa of area at least $11/5$ is dominated by a *balanced maximum sofa* with rotation angle $\pi/2$, a limit of area-maximizing polygons. Its cap satisfies an injectivity condition, which puts it in a convex space of caps where the area is bounded by a functional $Q$. By Mamikon's theorem, $Q$ is quadratic and concave, and its directional derivative at Gerver's cap is nonpositive in every direction, so Gerver's cap maximizes $Q$, where $Q$ equals the area of Gerver's sofa. That Gerver's sofa has area at least $11/5$ is an interval-arithmetic certificate checked by `decide +kernel`.

| Directory | Contents |
| --- | --- |
| `MovingSofa/Geometry`, `Motion`, `Sofa` | hallways, motions, rotation angle, monotone sofas |
| `MovingSofa/Convex`, `Curve`, `Analysis` | convex bodies, surface area measures, Jordan curves and Green's theorem, Lebesgue–Stieltjes calculus |
| `MovingSofa/Cap`, `Polygon`, `Bounds` | caps and niches, balanced polygons and their limits, the injectivity condition |
| `MovingSofa/Area` | Mamikon's theorem, the functional $Q$, its concavity and variation |
| `MovingSofa/Gerver` | Gerver's sofa: geometry, identification with the paper's set, area certificate |
| `MovingSofa/ForMathlib` | general lemmas not specific to the paper |

Formalizing the paper turned up 11 errors and gaps in its proofs and 33 misprints, all repaired here. None of them affects the main theorem. [`NOTES.md`](NOTES.md) lists them, along with how the formal statement compares with the paper and what is not formalized.

## Build

```sh
lake exe cache get
lake build
```

`Challenge.lean` gives three expected `sorry` warnings. The build can be quite slow, in part due to the vendored certificate.

Comparator accepts the solution against [`comparator.json`](comparator.json), including the nanoda kernel replay.

Licensed under [Apache-2.0](LICENSE); `vendor/gerver-sofa` is MIT.