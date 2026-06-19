# LeaTTa: the book

This is the LeaTTa book, a Verso manual that documents the MeTTa formalization in this repository. It
is its own small Lean project, kept separate from the main build, because it depends on Verso, and
through Verso on Mathlib and the Illuminate diagram library, which the kernel deliberately does not.

The book root is `Docs.lean` and the chapters are in `Docs/`. They cover the object language, the
minimal interpreter, the gradual type system, the metatheory, the operational semantics, the
kernel-to-specification correspondence, the blockchain-oriented guarantees, the future-work branch,
and a discussion of the current limitations.

## Build

```bash
cd book
export PATH="$HOME/.elan/bin:$PATH"
lake exe docs
```

The generated site lands in `book/_out/html-multi/`. Open `index.html` there.
