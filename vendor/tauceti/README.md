# Tau Ceti (ten files)

Ten files copied unchanged from [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) at commit `c52a81811e4626d2e9769fe9b0c701168c211332`, under Apache-2.0 (see `LICENSE`): the four modules this project imports (`Topology/JordanCurve/Path`, `Analysis/Normed/Module/FilledHull`, `Topology/EMetricSpace/BoundedVariation`, `Analysis/Calculus/MetricVariation`) and the six Tau Ceti modules they import.

They are vendored because Palomar requires a project that depends on Tau Ceti as a Git package to use exactly the Mathlib revision pinned in Tau Ceti's own manifest. At this commit Tau Ceti pins a Mathlib revision for Lean `v4.34.0-rc2`, and this project uses Mathlib `v4.35.0-rc1`.
