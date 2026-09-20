# Notes on the formalization

More detail than fits in the README: how the formal statement compares with the paper, the dependencies, the errors found in the paper, and what is not formalized.

## The statement

`Challenge.lean` copies its definitions and its three theorem statements from [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit `ddfbaf90f4482030d88aae5233fe933874296a23` (`FormalConjectures/Wikipedia/MovingSofa.lean`), and imports only Mathlib. The copied definitions and statements are unchanged. Four things differ from the original file:

- The `ℝ²` notation and the two plane instances are inlined from `FormalConjecturesForMathlib/Geometry/2d.lean` in formal-conjectures, with `Basis.orientation` renamed to `Module.Basis.orientation` to match current Mathlib.
- The anonymous `TopologicalSpace E(2)` instance is named `rigidMotionTopology`. Lean derives the name of an anonymous instance from its module, so without a fixed name Comparator would see different names in Challenge and Solution.
- The sanity tests in the original file, the `@[category …]` attributes, the `answer (…)` variant of the main theorem (it needs the formal-conjectures library) and the open conjecture `volume_eq_sofaConstant_iff_congruent_gerversSofa` (that Gerver's sofa is the only maximizer) are left out.
- Docstrings are added to the definitions that had none, such as Gerver's constants and the functions $r$, $x$, $y$ and $p$.

An AI review session, separate from the ones that wrote the proofs, compared the formal statement with the paper. It found the differences below. None of them weakens the theorem.

- The hallway is the same as in the paper. `horizontalHallway`, `verticalHallway` and `hallway` are the sets $H_L$, $V_L$ and $L = H_L \cup V_L$ defined there: closed infinite arms of width 1, with inner corner $(0,0)$ and outer corner $(1,1)$.
- The Challenge requires $m_0 = \mathrm{id}$ and $s \subseteq H_L$, whereas in the paper the initial motion $\Phi_0$ may be any translation. `canonical_paper_motion_bridge` shows that a sofa of either kind is a translate of one of the other kind. Translation preserves area, so the supremum is the same.
- Sofas are closed and connected, as in the paper's Definition 1.2. Disconnected shapes are not considered, either here or in the paper.
- Motions are elements of the full isometry group $E(2)$, whereas the paper works in $SE(2)$. Continuity and $m_0 = \mathrm{id}$ force every motion to preserve orientation (`motion_linear_det_pos`, `exists_motion_rotation`), so reflections never occur. The topology on $E(2)$ is proved to be the topology of pointwise convergence.
- Nothing is assumed about boundedness or measurability. `canonical_motion_compactness` proves that every moving sofa is compact, measurable and of finite area.
- The supremum is taken in `ℝ≥0∞`, with no `toReal`. It is proved to be finite, at least $11/5$ and attained, so the equation is between finite numbers.
- `ABφθSpec` uses $0 \le \varphi \le \theta \le \pi/4$, $0 \le A$, $0 \le B$, where Gerver, Romik and Baek use strict inequalities. Uniqueness on the closed domain is the stronger statement.
- `gerversSofa` is an intersection of rotated and translated hallways along Gerver's path, whereas in the paper $G$ is described by Romik's boundary curves. `gerver_canonical_paper_literal` proves that the two sets are equal.

Two things are not checked by Lean:

- The value of the area. The development proves `11/5 ≤ volume gerversSofa < ⊤`, and the certificate behind that bound gives $22007/10000 \le \lvert G\rvert$. There is no upper bound near $2.2196$. Evaluating the formulas in the Challenge in floating point gives $2.21953 \pm 10^{-5}$, which agrees with Gerver's $2.2195316\ldots$
- The transcription of Gerver's equations. `ABφθSpec` and the path functions $r, x, y, p$ were compared with Romik 2018, eqs. (1) to (4), and Gerver 1992, Theorem 2, only numerically: the published constants satisfy the four equations to about $10^{-16}$, and the area agrees to five digits. Nobody has compared them with the printed papers line by line.

## Dependencies

Every Git dependency is pinned to a full commit SHA in `lake-manifest.json`. In `lakefile.toml` Mathlib is required by its tag `v4.35.0-rc1` and the other three by commit. Mathlib is required last, so that its versions of shared transitive dependencies win. `vendor/gerver-sofa` has its own `lean-toolchain`, which Lake ignores.

| Input | Revision | Licence | What is taken |
| --- | --- | --- | --- |
| Mathlib | `c32e1ec0d1eb5237ba344eee50162f45d5b0fc76` (`v4.35.0-rc1`) | Apache-2.0 | Everything else |
| Tau Ceti | `c52a81811e4626d2e9769fe9b0c701168c211332` | Apache-2.0 | `isJordanCurve_range_union_range_of_inter_eq_pair` (a Jordan curve from two concatenated arcs meeting in their endpoints), `filledHull_subset_closedConvexHull`, and lemmas on bounded variation |
| lean-pool | `bb74ee07fc23bc81358d75a9c40303e5e27fced8` | Apache-2.0 | `brunn_minkowski_euclideanSpace`, Jonathan Ho's Brunn–Minkowski inequality and its Prékopa–Leindler prerequisites |
| jordan_pick | `b3c9b7cf7358bf81a077d78ad67e6e8247869ddd` | Apache-2.0 | The Jordan curve theorem (`JordanCurve.step_A_exists_bounded`, `step_B_bounded_unique`, `exists_unbounded_component`, `component_boundary_eq`, `isOpen_component`, over `JordanCurve.Brouwer.brouwerFPT`), assembled into `MovingSofa.jordan_separation` |
| GerverSofaLean | `vendor/gerver-sofa`, from the v1.1.0 release archive (SHA-256 `7c496150f709ac709ae01f4836e9a702a18f752450efa69f15cf44264c0c2f77`) | MIT, © 2026 Dawid Trela | Kernel-checked existence and uniqueness of Gerver's parameters (`PartF.Parameters.existsUnique`, global interval exclusion plus a Krawczyk certificate), admissibility of Gerver's sofa, the certified parameter enclosures, and certified transcendental soundness |
| leancert | `571a228555ae38742448854be81d7b59d994a8e3` | Apache-2.0 | Interval-arithmetic support required by the vendored certificate |

GerverSofaLean is vendored because its v1.1.0 Git tag lacks the Part F bridge that the release archive has. One proof in its final motion module was adjusted for Mathlib `v4.35.0-rc1` (it unfolds the sofa constant before applying a supremum bound). No statement or definition changed. `MovingSofa/Canonical/GerverDefinitions.lean` and `MovingSofa/Gerver/Motion.lean` adapt its proofs to the Challenge definitions and keep Dawid Trela's MIT notice.

The code written for this project is Apache-2.0. The paper and its figures are not covered by this licence.

## Differences from the paper

This section lists the problems found in the paper and the places where the Lean proof takes a different route.

### Errors and gaps in the paper

While formalizing, 76 places were recorded where the Lean statement or proof departs from the printed text. A second pass went through all 76 against the paper's LaTeX source to separate real problems from precision that only a formalization needs. It found 11 errors and gaps that need a new argument or a new hypothesis, and 33 misprints that are mathematically wrong as printed but have an evident fix. Both are listed below. The other 32 are left out: 16 are typos with no mathematical content (a wrong letter, a stray prime, a wrong cross-reference), 13 are conventions or domains that a formalization has to spell out, and 3 were not errors. None of this affects the truth of the main theorem. The numbers are those of the original list of 76, so they have gaps. Labels are the paper's LaTeX labels.

Errors and gaps:

| # | Paper label | Problem | What is done here |
| --- | --- | --- | --- |
| P02 | `thm:surface-area-measure` | The identity $\sigma_K(X) = \mathcal{H}^1\bigl(\bigcup_{t \in X} e_K(t)\bigr)$ fails for flat bodies, which are convex bodies under the paper's definition. A segment of length $l$ has surface measure $2l$, but the union of its edges has length $l$. | Segment multiplicities corrected, and the identity proved for bodies with interior and for short arcs. |
| P04 | `thm:injectivity-gerver` | The printed proof claims that Gerver's sofa is a limit of maximum polygon sofas, and hence a balanced maximum sofa. A balanced maximum sofa has maximum area, which is the main theorem, and this theorem is used in the proof of the main theorem. A remark after the theorem acknowledges that one inequality was checked only numerically. | The three injectivity conditions are proved directly for Gerver's sofa: surface densities, a $C^1$ corner path, and strict frame velocities. |
| P05 | `thm:gerver-monotone` | The contact and wall geometry of Gerver's sofa, on which the rest of the argument rests, is stated with no proof. The following remark cites numerical evidence and says a symbolic verification would be worthwhile. The contact derivatives are also only one-sided at the switch angles. | Proved here from support, roof and derivative results for each stage, with $B$ and $D$ piecewise $C^1$. |
| P15 | `lem:modulo-linear-const` | A convex domain has only barycentric combinations, so $K + c$ is not defined, and being affine in each slot does not give the additive expansion the proof uses. The lemma is never used in the paper. | Not needed. Over a real vector space with a bilinear form the lemma is true, with an affine difference. |
| P16 | `thm:simple-nef-polygon` | Nef polygons may be unbounded (a half-plane is one), and then the areas and edge lengths in the statement are infinite and the Lipschitz step of the proof fails. | Boundedness under small perturbations added as a hypothesis. Every application satisfies it. |
| P26 | `pro:curve-area-functional-additive` | The printed proof stops in the middle of a sentence. The missing part also has to show that the concatenation is rectifiable and that the curve area does not depend on the parametrization. | Invariance under monotone surjections proved from Stieltjes increments, and the path integral split over a partition. |
| P35 | `thm:limiting-maximum-cap-connected` | The proof passes to a Hausdorff limit of the open polygon niches. Uniform convergence of support functions does not give that: a wedge can appear or vanish in the limit. | Replaced by a direct argument from strict quadrant membership, density of the dyadic angles, and closedness of the limit cap. |
| P46 | `lem:right-left-body` | The proof assumes that the upper boundary of a cap in the class $\mathcal{K}^i$ avoids its niche. The upper stadium $[-2,2] \times \{0\}$ plus the upper unit half-disk satisfies all three injectivity conditions and has area above $11/5$, yet the point $(0, 3/2)$ lies in its niche and not in the cap. | The endpoint support is proved directly, with an explicit reflection for the left tail. The class is unchanged. |
| P51 | `lem:upper-boundary-tracing` | The area theorem for convex arcs is applied to an arc of angular length exactly $\pi$. The theorem needs length below $\pi$, because the cut lemma behind it needs the cone $H_K(a) \cap H_K(b)$ to have a vertex. | The area integral is split into four short arcs and the singleton at $\pi/2$. |
| P57 | `lem:leg-bounded` | A containment theorem proved for limiting caps is applied to a finite polygon cap, which is not such a limit. | Replaced by the polygon niche containment at the grid angle $\pi/4$ and explicit vertex distances. |
| P63 | `thm:leg-length-bounds` | A differentiation formula for the one-sided arm length $f^+$ is applied to $f$ on the closed interval. At $\pi/2$ the two differ by the length of the top face, and that endpoint is not checked. | Integrated on $(0, t]$ for $t < T$ and passed to the limit by continuity of the support function. |

Misprints:

| # | Paper label | What is wrong |
| --- | --- | --- |
| P01 | `pro:lebesgue-stieltjes-abs-cont` | The density of an absolutely continuous function is said to be bounded. It is only integrable: $\sqrt{t}$ on $[0,1]$ is a counterexample. |
| P07 | `def:left-right-derivative` | $\partial^+$ is defined as the left derivative and $\partial^-$ as the right, and then both are used the other way round everywhere. |
| P10 | `pro:mirror-reflection` | The list of mirror identities forgets that reflection swaps the two walls and the two wedge end points, and one display reflects the body twice. |
| P11 | `pro:cap-tangent-arm-mirror` | The mirror identity for arm lengths keeps $t$ on both sides, although reflection sends $t$ to $\pi/2 - t$. |
| P14 | `thm:variation-a2-gerver` | Two cases of the final variation computation say nonnegative where the inequality gives nonpositive, which is also what the theorem needs. One case cites the wrong interval, and the tail support functions lose their opposite-angle accent. |
| P17 | `lem:lower-bound-sequence` | The induction step writes $f_K$ where $f_n$ belongs, and credits a newly proved inequality to the induction hypothesis. |
| P18 | `lem:balancing` | In the endpoint case the change in niche area has the sign of a growing region, although the region shrinks. The formula in the statement of the lemma is correct. |
| P19 | `def:mamikon-right-left` | The right Mamikon region starts at $\pi/2 + \varphi^R$. It should start at $\pi + \varphi^R$ to match the tail it measures. |
| P20 | `lem:mamikon-middle-eq` | Two segment areas are miscomputed: one drops a factor $1/2$ and the other uses the wrong support value. The conclusion is unaffected. |
| P21 | `lem:linvals` | One clause evaluates a two-argument function at the same argument twice, which makes it false as printed, and the remainder integrals have the wrong limits. They should run over $[\varphi^R, \varphi^L]$. |
| P27 | `lem:vertex-bounded-variation` | The last interval in the proof is wider than a quarter turn, and the claimed monotonicity of the vertex is false on it (take the unit disk). Quarter turns were meant. |
| P30 | `lem:lower-bound-threshold` | The conclusion is stated up to $1$, although the proof and the only use need $(0, \pi/2]$. |
| P31 | `thm:balanced-consumed` | The statement gives membership in the closed inward quadrant. The proof gives the open quadrant, and the next theorem uses the open one. |
| P32 | `lem:calculation-inequalities` | The lemma starts at $\arctan(11/5)$, but its use starts at the smaller angle $\operatorname{arcsec}(11/5)$. One endpoint check gives exactly $1$, so strictness needs a convexity argument with weight below one. |
| P34 | `def:angled-niche` | The polygon niche is clipped by the parallelogram $P_\omega$. It should be the fan $F_\omega$. As printed, a family of caps of unbounded width keeps an area gap of $2\sqrt{2}$, which contradicts the boundedness lemma. Every later use in the paper assumes the fan. |
| P36 | `thm:niche-in-cap` | In the reverse implication the hypothesis is written with the containment the wrong way round. |
| P37 | `lem:polygon-cap-bounded` | The lemma assumes positive area, and the existence proof that uses it needs nonnegative area. The estimate in the proof already gives the stronger version. |
| P38 | `thm:balanced-maximum-cap` | The diameter of a cap of width $c$ is given as $\sqrt{1+c}$ and should be $\sqrt{1+c^2}$. The check that a Hausdorff limit of caps is a cap is called easy and left out. |
| P40 | `thm:monotonization-is-connected` | The line section of the niche is removed by subtracting $l_\theta \setminus X$, which is the wrong half-line. It should be $l_\theta \cap X$. |
| P41 | `lem:niche-in-cap` | One case claims a contradiction from a corner that is not in the open fan. A cap point can lie on the fan boundary (every cap contains the fan vertex). The wedge is then empty, so the lemma holds. |
| P42 | `thm:cap-hallway-intersection` | The two closure directions are named with the wrong sign, and the right-angle intersection is never shown to be bounded. |
| P43 | `thm:convex-body-linear` | The system of supporting lines is solved with $U^{-1}$ and should use $(U^{\mathsf T})^{-1}$. The conclusion is unaffected. |
| P44 | `pro:measure-translation` | Clause (4) puts the surface measure of the lower $D$ boundary a quarter turn from where it lives. |
| P45 | `lem:monotonicity-intervals` | The cone $H^d(t) \setminus H^b(t)$ is described with both spanning directions reversed. With the printed signs the disjointness step fails. |
| P48 | `lem:convex-curve-cut` | Three local errors: the cone opening is $\pi - (b - a)$, not $b - a$; a displayed difference has the wrong sign; and an end face is said to be cut by $K$, where the cutting half-plane is meant. |
| P50 | `thm:mamikon` | The proof sets $z - w = \alpha v_t$ and then substitutes $\alpha u_t$ in the last step. The value is unchanged. |
| P53 | `lem:wedge-gap-limit` | The wedge vertex is placed on the outer supporting line, without the unit offset to the inner wall. |
| P54 | `pro:cap-trans-space` | Condition (2) lists only normals with positive vertical component, so no bounded polygon satisfies it. The lower normals $\omega + \pi$ and $3\pi/2$ are missing. |
| P55 | `thm:balanced-polygon-sofa-connected` | A displacement along the lower polyline has its sign reversed, and the next display reverses it back. |
| P56 | `lem:leg-convergence` | Atoms of the surface measure are excluded at $t$, but the quantity compared jumps at $t + \pi/2$. |
| P60 | `thm:balanced-ineq-limit` | Both integrands subtract the approximating arm function from itself. The limiting one is meant. |
| P69 | `pro:omega-gap` | The proof uses the point $o_\omega - v_\omega$ where it needs $o_\omega - u_\omega$, so its second triangle is not a right triangle. The identities are correct. |
| P76 | `pro:rotating-hallway-parts` | One inner-quadrant formula drops the $-1$ from its second wall offset, which contradicts the inner corner in the same proposition. |

### Where the proof takes a different route

- The area facts of Green and Minkowski type, which are quoted in the paper, are proved here.
- Several arguments by Stieltjes measures and compact exhaustion become arguments about exposed edges. The two inactive tail windows of Gerver's cap have measure zero because a single exposed edge carries the whole window. The same idea removes the constant-vertex exhaustion from the area variation for special caps.
- The numerical area bounds come from the integer interval certificate in `MovingSofa/Gerver/Area`, which uses the vendored certified enclosure of $\pi$. In the paper $\pi$ is recomputed from a series.
- The signed area of Gerver's niche comes from an identity between the curve area and the area of a Jordan interior, in place of a monotone-roof theorem and a limit of square coverings.
- The middle estimate for caps needs only one monotone roof loop. The original argument has two Jordan curves and applies the Jordan curve theorem.
- The null-image and exterior-winding facts for Jordan curves of bounded variation are proved without Jordan separation.
- The connectedness criterion uses horizontal extrema and a vertical fibre, in place of the two end points of the cap and a ray argument.
- Disjointness of the left and right parts of a cap is proved from coordinate inequalities, without the two parallelograms of the paper.
- Hausdorff containment uses a lemma with a fixed target, followed by a limit specific to caps.
- The paper's subscripted $O$-notation is replaced by explicit constants and thresholds, which is stronger.

## What is not formalized

The paper has 286 numbered environments: definitions, lemmas, theorems and so on. Twenty have no Lean counterpart. None of the compared theorems depends on any of them.

| Paper label | Why there is no Lean counterpart |
| --- | --- |
| `thm:gerver` | Gerver 1992, Theorem 1, quoted for exposition. Clauses (i) and (ii), that a movable region with rotation angle in $[\pi/3, \pi/2]$ exists and has maximal area, are proved here in stronger form. Clauses (iii) and (iv), that the balanced polygons $P_n = \bigcap_{k \le n} H_{k\gamma/n}$ approximate Gerver's sofa, are not. They would need the area maximizer among right-angle caps to be unique, and the paper's main theorem gives only the maximum value. This may need new mathematics. |
| `pro:tangent-hallway` | States that $L_S(t)$ is the unique translate of $R_t(L)$ whose outer walls are the two tangent lines of $S$. The main theorem does not need it, and it is not proved here. |
| `pro:wedge` | The niche is the union of its wedges. Inlined at each of its four uses. |
| `lem:cap-ends-not-in-niche` | Replaced by horizontal extrema and a rectangle bound. |
| `thm:monotonization-idempotent` | Only the inequality is used. The equality is proved inline. |
| `thm:injectivity-abridged` | An abridged version of `thm:injectivity`, stated in the paper's first chapter. The full theorem is proved here. |
| `lem:hausdorff-distance-containment` | Replaced by a Hausdorff lemma with a fixed target and a limit specific to caps. |
| `lem:convex-curve-concat` | Replaced by a decomposition of measures on the circle of normals. |
| `pro:curve-area-functional-quadratic` | Proved in stronger form as the first part of `curveArea_variation`. Only the named bilinear form has no definition of its own. |
| `lem:modulo-linear-const` | Never referenced in the paper. The relation is proved directly at its two uses. |
| `def:sofa-boundaries-intro` | The contact points $A$, $C$ are total functions here. $B$, $D$ for general caps are absent because nothing uses them. |
| `def:rotating-hallway-parts-intro` | Repeats a later definition, which is formalized. |
| `lem:cap-right-left-parallelogram`, `def:cap-right-left-parallelogram` | Used at most once. The geometric content is proved for the strip parallelogram anchored at the origin. |
| `def:closed-in-direction` | Its two uses are proved without the ray argument. |
| `def:further-in-direction` | Notation for an inner-product inequality. |
| `def:line-half-plane-directions` | Notation for a half-plane that already exists. |
| `def:mamikon-region` | Never referenced. It is replaced immediately by the Mamikon number, and the region's area identity is not proved in the paper either. |
| `def:o-notation-subscript` | Replaced throughout by explicit constants. |
| `def:right-triangle` | Never referenced. Its content is one trigonometric identity. |

The count comes from a mechanical pass by an AI review session. It checks, clause by clause, that every environment the main theorem uses has a Lean counterpart. It does not re-verify the informal arguments. The same pass lists 13 places where the paper may be ambiguous, all outside what the compared theorems use.
