# Optimality of Gerver's sofa

This repository contains a Lean 4 proof that Gerver's sofa has the largest area of any shape that can be moved around a right-angled corner in a hallway of width one. This is the moving sofa problem, solved by Jineon Baek in [*Optimality of Gerver's Sofa*](https://arxiv.org/abs/2411.19826) (2024).

```lean
theorem MovingSofa.sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa
```

- The statement is copied from Google DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) and passes [comparator](https://github.com/leanprover/comparator).
- The statement is formalized unconditionally: the Green-type curve area identity and the Minkowski-type mixed area facts that the paper quotes are proved here.
- The proof is about 66,000 lines of Lean, not counting dependencies. It was written in about four days by AI coding agents (OpenAI Codex and Claude Code), directed by Dean Cureton.

## Built on

- **[Jineon Baek's paper](https://arxiv.org/abs/2411.19826)**: followed step by step
- **[GerverSofaLean](https://github.com/dawidmtrela-dotcom/GerverSofaLean)** by Dawid Trela: Gerver's four constants exist and are unique, and Gerver's sofa really does get around the corner. Vendored in `vendor/gerver-sofa` (v1.1.0, MIT, patched for current Mathlib)
- **[formal-conjectures](https://github.com/google-deepmind/formal-conjectures)**: the formal statement ([`MovingSofa.lean`](https://github.com/google-deepmind/formal-conjectures/blob/ddfbaf90f4482030d88aae5233fe933874296a23/FormalConjectures/Wikipedia/MovingSofa.lean))
- **[lean-pool](https://github.com/Vilin97/lean-pool)**: Jonathan Ho's Brunn–Minkowski ([`BrunnMinkowski.lean`](https://github.com/Vilin97/lean-pool/blob/bb74ee07fc23bc81358d75a9c40303e5e27fced8/LeanPool/Isoperimetric/BrunnMinkowski.lean)), vendored in `vendor/lean-pool`
- **[jordan_pick](https://github.com/rkirov/jordan_pick)**: the Jordan curve theorem ([`JordanCurve.lean`](https://github.com/rkirov/jordan_pick/blob/b3c9b7cf7358bf81a077d78ad67e6e8247869ddd/JordanPick/JordanCurve.lean))
- **[TauCeti](https://github.com/TauCetiProject/TauCeti)**: Jordan curves from two arcs ([`Path.lean`](https://github.com/TauCetiProject/TauCeti/blob/c52a81811e4626d2e9769fe9b0c701168c211332/TauCeti/Topology/JordanCurve/Path.lean)), filled hulls ([`FilledHull.lean`](https://github.com/TauCetiProject/TauCeti/blob/c52a81811e4626d2e9769fe9b0c701168c211332/TauCeti/Analysis/Normed/Module/FilledHull.lean)), bounded variation ([`BoundedVariation.lean`](https://github.com/TauCetiProject/TauCeti/blob/c52a81811e4626d2e9769fe9b0c701168c211332/TauCeti/Topology/EMetricSpace/BoundedVariation.lean), [`MetricVariation.lean`](https://github.com/TauCetiProject/TauCeti/blob/c52a81811e4626d2e9769fe9b0c701168c211332/TauCeti/Analysis/Calculus/MetricVariation.lean)), vendored in `vendor/tauceti`
- **[Mathlib](https://github.com/leanprover-community/mathlib4)**

## What's proved

The hallway is $(-\infty,1] \times [0,1] \cup [0,1] \times (-\infty,1]$. A *moving sofa* is a nonempty closed connected set in the horizontal arm, plus a continuous family of rigid motions that starts at the identity, keeps the set inside the hallway, and ends with it in the vertical arm. `sofaConstant` is the supremum of the areas of moving sofas. The theorem above is Theorem 1.1 of the paper.

Comparator checks two more theorems:

- `MovingSofa.GerversSofa.ABφθSpec.existsUnique`: the four equations for Gerver's constants $A, B, \varphi, \theta$ have exactly one solution; `gerversSofa` is defined from it
- `MovingSofa.isMovingSofa_gerversSofa`: Gerver's sofa is itself a moving sofa, so it attains the supremum

Two caveats: the statement fixes $m_0 = \mathrm{id}$ where the paper allows a translate (proved equivalent), and the area of Gerver's sofa is only shown to be $\ge 11/5$; the actual value $2.2195\ldots$ isn't checked.

## The proof

The proof follows the same route as the paper. Any sofa of area $\ge 11/5$ is dominated by a *balanced maximum sofa* with rotation angle $\pi/2$, a limit of area-maximizing polygons. Its cap satisfies an injectivity condition, which lands it in a convex space of caps where area is bounded by a functional $Q$. Mamikon's theorem makes $Q$ quadratic and concave, and the directional derivative of $Q$ at Gerver's cap is $\le 0$ in every direction, so Gerver's cap maximizes $Q$. There $Q$ is exactly the area of Gerver's sofa. The $11/5$ bound for Gerver's sofa is an interval-arithmetic certificate checked by `decide +kernel`.

| Directory | Contents |
| --- | --- |
| `MovingSofa/Geometry`, `Motion`, `Sofa` | hallways, motions, rotation angle, monotone sofas |
| `MovingSofa/Convex`, `Curve`, `Analysis` | convex bodies, surface area measures, Jordan curves and Green's theorem, Lebesgue–Stieltjes calculus |
| `MovingSofa/Cap`, `Polygon`, `Bounds` | caps and niches, balanced polygons and their limits, the injectivity condition |
| `MovingSofa/Area` | Mamikon's theorem, the functional $Q$, its concavity and variation |
| `MovingSofa/Gerver` | Gerver's sofa: geometry, matching it with the paper's set, area certificate |
| `MovingSofa/ForMathlib` | general lemmas, nothing sofa-specific |

Formalizing the paper surfaced 11 small errors/gaps in the paper's proofs, and 33 misprints. These are all repaired here, and none of them break the main theorem. See [`NOTES.md`](NOTES.md) for more details.

## Build

```sh
lake exe cache get
lake build
```

`Challenge.lean` gives three expected `sorry` warnings. The build can be quite slow, in part due to the vendored certificate.

Comparator accepts the solution against [`comparator.json`](comparator.json), including the nanoda kernel replay.

Licensed under [Apache-2.0](LICENSE), `vendor/gerver-sofa` is MIT.