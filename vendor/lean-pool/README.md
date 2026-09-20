# lean-pool (three files)

`LeanPool/Isoperimetric/Basic.lean`, `PrekopaLeindler.lean` and `BrunnMinkowski.lean`, copied unchanged from [Vilin97/lean-pool](https://github.com/Vilin97/lean-pool) at commit `bb74ee07fc23bc81358d75a9c40303e5e27fced8`. They are Jonathan Ho's proof of the Brunn–Minkowski inequality, under Apache-2.0 (see `LICENSE`).

They are vendored because the package is called `lean-pool`, which Lake writes into `lake-manifest.json` as `«lean-pool»`, and Palomar's verifier does not accept that name.
