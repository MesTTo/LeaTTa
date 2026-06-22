# Installing and running LeaTTa

LeaTTa ships the minimal MeTTa interpreter as a single native binary named `LeaTTa`. It
links only against the standard C library, so a prebuilt bundle runs without installing
Lean or Mathlib.

## Platforms

The prebuilt Linux x86_64 binary is the tested target. The binary runs on any glibc Linux of the
same architecture. macOS and Windows are supported through the source build below. The
release workflow (`.github/workflows/release.yml`) produces binaries for Linux, macOS,
and Windows on each tagged release.

## Option 1: prebuilt release (recommended, Linux x86_64)

Download the archive for your platform from the
[releases page](https://github.com/MesTTo/LeaTTa/releases), then unpack and install it:

```bash
tar xzf leatta-1.0.5-linux-x86_64.tar.gz
cd leatta-1.0.5-linux-x86_64
./install.sh                 # installs to ~/.local/bin by default
```

To install system wide instead, pass a prefix: `sudo ./install.sh /usr/local`.

If `~/.local/bin` is not on your PATH, add it:

```bash
echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.bashrc && source ~/.bashrc
```

Then test it:

```bash
LeaTTa --min '!(+ 1 (* 2 (- 10 4)))'      # [13]
LeaTTa --oracle examples/a1_symbols.metta
```

## Option 2: build from source (Linux, macOS, Windows)

Building from source requires the Lean toolchain, managed by [elan](https://github.com/leanprover/elan). The
exact toolchain version is pinned in `lean-toolchain`.

```bash
elan toolchain install $(cat lean-toolchain)   # if you do not already have it
lake exe cache get                             # prebuilt Mathlib, used by the metatheory layer only
lake build LeaTTa                              # builds just the interpreter binary
```

The binary lands at `.lake/build/bin/LeaTTa` (`LeaTTa.exe` on Windows). Install it with:

```bash
make install                                   # copies it to ~/.local/bin
```

Mathlib backs the metatheory proofs only. The interpreter binary does not link Mathlib,
so once `LeaTTa` is built it runs anywhere without the proof layer.

## Usage

`LeaTTa` runs programs on the minimal interpreter. For each `!`-evaluation, it prints the
list of values it produces.

| Command | What it does |
| --- | --- |
| `LeaTTa` | run the built-in demo |
| `LeaTTa --min 'PROGRAM'` | run a program given on the command line |
| `LeaTTa --file PATH` | run a `.metta` source file |
| `LeaTTa --oracle PATH` | run a test file's `!`-assertions and report PASS/FAIL/TOTAL |

An assertion passes under `--oracle` when it evaluates to the unit atom `()`.

Examples:

```bash
LeaTTa --min '!(map-atom (1 2 3) $x (* $x $x))'   # [(1 4 9)]
LeaTTa --min '!(case (+ 1 1) ((1 one) (2 two)))'  # [two]
LeaTTa --file examples/test_stdlib.metta
```

## Reproducing the validation

From a source checkout:

```bash
make oracle        # differential oracle against Hyperon's corpus, 270/270
make regression    # stdlib and grounded-op feature tests
make test          # both of the above
```

## Building a release bundle

Maintainers can rebuild the distributable archive for the current platform:

```bash
make release       # writes dist/leatta-<version>-<platform>.tar.gz and its .sha256
```
