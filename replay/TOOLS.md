# Replay tools: obtaining, building, pointing the driver at them

`scripts/replay.sh` (= `python3 replay/replay.py`) needs three external programs:

| Role | Program | Upstream | Pinned commit |
|---|---|---|---|
| Export | `lean4export` (export format 3.1.0) | https://github.com/leanprover/lean4export | `411dce7db58a3afc60ecab2d211acd1042b593dc` |
| Second kernel | `nanoda_bin` (nanoda_lib 0.4.16) | https://github.com/ammkrn/nanoda_lib | `05055695879dfebb6628a67da88ceca6cd6b0421` |
| Statement check (optional) | `replay-comparator` = Comparator library + `tools-src/ComparatorWorker.lean` | https://github.com/leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` (library files identical to the harness's `14b5039e…`, see below) |

Pins are recorded in `replay/tools.lock.json`. The commit is the pin. Binary hashes depend on
platform and compiler and are recorded per run in the receipt.

Everything else comes from the project itself: Lean 4.33.1 via `lean-toolchain`, the built
`JocelynWorkspace` environment via `lake env`, and Python 3 (standard library only).

## 1. lean4export and replay-comparator (Lean 4.33.1)

lean4export reads `.olean` files, so it must be compiled with the same Lean as the release
(4.33.1, githash `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). Upstream `lean-toolchain` at the
pinned commit is v4.34.0-rc2. Do not use a binary built with a different toolchain.

`replay/tools-src/` is a small, separate Lake project (`lean-toolchain` = v4.33.1) that requires
both repositories. Its `lake-manifest.json` pins the exact revisions.

```sh
cd replay/tools-src
lake build replay-comparator @lean4export/lean4export     # about 1–2 min; needs network for the two clones
mkdir -p ../_tools
cp .lake/packages/lean4export/.lake/build/bin/lean4export ../_tools/lean4export
cp .lake/build/bin/replay-comparator                       ../_tools/replay-comparator
```

Pitfalls, all observed while writing this:

* **Never run `lake update` without `--keep-toolchain` here.** When Lake writes a manifest from
  scratch it "updates" the root `lean-toolchain` to the newest dependency toolchain
  (v4.34.0-rc2), then downloads that toolchain (about 2.7 GB). Use the committed
  `lake-manifest.json`. If you must re-resolve, run `lake update --keep-toolchain` and re-check
  the pins below.
* **Resolution overrides the root pin.** A fresh resolution took lean4export from Comparator's
  own manifest (`b18d673…`, one commit before the pinned merge `411dce7`, which carries the
  "partial is unsafe" exporter fix) instead of the root `[[require]]`. The committed manifest has
  lean4export at `411dce7db58a3afc60ecab2d211acd1042b593dc` with `"inherited": false`. After any
  update, check with `git -C .lake/packages/lean4export rev-parse HEAD`.
* **The Comparator commit cannot be cloned.** `14b5039e…`, which the research harness used, is
  the head of the unmerged upstream PR #78 ("fix: contain sandbox descendants with util-linux").
  No branch reaches it, so Lake's clone fails with `reference is not a tree`. The only Comparator
  files built here are `Comparator/Util.lean`, `Comparator/Axioms.lean` and
  `Comparator/Compare.lean`. They are byte-identical at `14b5039e`, at `575674928e239f5bc452aab72d1dd7b0f1326494`
  (the merge of PR #75 into master and the merge-base) and at master `fd5d5bc` (checked with `git diff`).
  `tools-src` therefore pins `57567492…`. `git fetch origin 14b5039e0b6a5171afa160920984e521817d4138`
  does work if you want to verify this yourself.
* Upstream Comparator `Main.lean` (which uses the `landrun` sandbox, Landlock, Linux only) is not used.
  `ComparatorWorker.lean` is the Jocelyn research harness's worker, copied verbatim (sha256
  `f2d81a7df1a6125d92a86fe1d9c2e233aaf44feb20421d43816b07da3708857a`). Given one reference
  (statements) export, one candidate export and one theorem name, it runs
  `Comparator.compareAt` (statement plus the complete definition closure) and then
  `Comparator.checkAxioms`, which admits only `propext`, `Quot.sound` and `Classical.choice`.
  It performs no kernel replay (`builtin_kernel_replay: false`). Nanoda does that.

Equivalent manual build (what the harness did; no Lake). With the 4.33.1 toolchain's `lean` and
`leanc`, compile `Export.lean`, `Export/Parse.lean`, `Main.lean` (lean4export) and
`Comparator/{Util,Axioms,Compare}.lean`, `ComparatorWorker.lean` with `lean -R <src> -o X.olean -c X.c`.
Then compile each file with `leanc -O2 -c` and link it with `leanc -O2 -leanshared`.

## 2. Nanoda

```sh
cargo install --git https://github.com/ammkrn/nanoda_lib \
  --rev 05055695879dfebb6628a67da88ceca6cd6b0421 --locked \
  --root replay/_tools            # binary: replay/_tools/bin/nanoda_bin
```

`--locked` uses the repository's `Cargo.lock` (sha256 `892346d3da3a6d728b34447e4cd8b6f063ac6acd9b514262000d85d58d17d9e4`).
The rustc version used for the recorded receipt's binary was not recorded by the harness. The
local toolchain at the time was rustc 1.98.1. The driver runs Nanoda with a 63 MiB stack limit
(`ulimit -s 64512`, the harness value).

## 3. Pointing the driver at the binaries

Each tool is looked up in this order:

1. an environment variable: `REPLAY_EXPORTER`, `REPLAY_NANODA`, `REPLAY_COMPARATOR`;
2. `--tools-json FILE`, a `jocelyn.proof-replay-tools.v1` file with `{exporter,kernel,comparator}.{path,sha256}`
   and `source_commits`. The driver refuses a binary whose sha256 differs from that file;
3. `replay/_tools/lean4export`, `replay/_tools/bin/nanoda_bin`, `replay/_tools/replay-comparator` (gitignored).

```sh
REPLAY_EXPORTER=$PWD/replay/_tools/lean4export \
REPLAY_NANODA=$PWD/replay/_tools/bin/nanoda_bin \
REPLAY_COMPARATOR=$PWD/replay/_tools/replay-comparator \
  scripts/replay.sh --skip-build
```

The receipt records every binary's path, how it was found, its sha256, its upstream repository
and its commit.

## 4. Running the replay and reading the receipt

```sh
scripts/replay.sh --skip-build                 # after scripts/build.sh; every declaration, every statement file
scripts/replay.sh                              # the same, compiling first with scripts/build.sh
scripts/replay.sh --local-deps --skip-build    # accept linked packages (recorded as local-deps)
scripts/replay.sh --help
```

By default the driver compares every statement file under `replay/statements/`, one file
at a time, and fails if `.lake/packages` is a symbolic link (a fresh clone fetches the
pinned dependencies itself). It never runs `lake build`. The sequence from a fresh clone
to a registered result is in the README, section "Reproducing the checks".

The declarations are read from `release/manifest.json`. Before any Nanoda run the driver
checks every Lean audit row against the manifest (statement hash, exact axiom set, exact
`native_decide` axiom list, evidence level) and fails on any difference.

Each lean4export export is deleted as soon as Nanoda (or Comparator) has consumed it, and
the driver aborts before an export if free disk is below `--min-free-gib` (default 6).
Exports of the combined standard-axiom set are several hundred MB.

The receipt (`replay/receipts/replay-<time>-<commit>.json`) contains no absolute paths:
repository files are recorded relative to the repository root, the work directory as
`<work>`, the home directory as `~`, and tools by their repository-relative path (or
`<external>/<name>`) together with their sha256, upstream repository and pinned commit.
It records the dependency mode (`clean-clone` or `local-deps`), the revisions checked out
under `.lake/packages`, the Lean githash, the build result (warning count), each
declaration's audit and Nanoda verdicts, each export's sha256 and size, the Nanoda
configuration hashes, the Comparator verdicts and the elapsed time of every stage.

The research harness's prebuilt binaries and binaries built from source as above have given
byte-identical exports and identical verdicts. Binary hashes differ across machines and link
steps; the commit is the pin.

## 5. What the checks mean

* **Nanoda, standard pass**: `permitted_axioms` = `propext`, `Classical.choice`, `Quot.sound`,
  with `unpermitted_axiom_hard_error: true`, `nat_extension` and `string_extension` on
  (GMP-style literal arithmetic, as in Lean's kernel). A pass means Nanoda type-checked every
  declaration in the export: the release theorems, their whole dependency closure (Mathlib
  included) and the kernel primitive roots. The export contains no other axiom.
* **Nanoda, native pass** (declarations that use `native_decide`): the permitted list also
  contains exactly that declaration's own `…._native.native_decide.ax_*` auxiliary axioms, spelled
  as raw export names with macro scopes, as Nanoda compares them. Nanoda cannot evaluate compiled
  code. Each such axiom states one closed decidable proposition, which Lean established by running
  compiled code, and Nanoda takes it as given. The standard-only probe on the same export is
  expected to fail, and it demonstrates that the native axioms really are present.
* **Comparator**: the statement in the statements file (`theorem <FullName> : … := by sorry`) must
  equal the built declaration's type, and every constant reachable from it (definitions included)
  must be identical in both exports. Trust assumption: whatever the statements file imports.
