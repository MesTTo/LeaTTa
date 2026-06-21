# LeaTTa: the book

The LeaTTa book is a Verso manual that documents the MeTTa formalization in this repository. It is
its own Lean project, kept separate from the main build because it depends on Verso, and through
Verso on Mathlib and the Illuminate diagram library, which the kernel does not import.

The book root is `Docs.lean` and the chapters are in `Docs/`. They cover the object language, the
minimal interpreter, the gradual type system, the metatheory, the operational semantics, the
kernel-to-specification correspondence, the blockchain-oriented guarantees, the MeTTaIL runtime path,
the Cordial Miners safety core, future work, and current limitations.

## Build

```bash
cd book
export PATH="$HOME/.elan/bin:$PATH"
lake exe docs
```

The generated site lands in `book/_out/html-multi/`. Open `index.html` there.
