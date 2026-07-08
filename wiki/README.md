<!-- SPDX-FileCopyrightText: 2026 MesTTo -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Wiki source

These pages mirror the project's GitHub wiki. They are version-controlled here so they
can be reviewed alongside the code.

- `Home.md` is the wiki landing page. It points readers to the documentation.
- `Developer-Guide.md` covers the Lean toolchain, libraries, and proof machinery for
  contributors.
- `Mechanization-Ledger.md` maps public claims to checked Lean declarations.
- `Axiom-Catalog.md` records the human-readable assumption surface.

## Publishing to the GitHub wiki

GitHub creates the wiki git repository only after the first page is made in the browser.
Open `https://github.com/MesTTo/LeaTTa/wiki`, click "Create the first page", and save.
After that, publish these pages with:

```bash
git clone https://github.com/MesTTo/LeaTTa.wiki.git
cp wiki/Home.md wiki/Developer-Guide.md wiki/Mechanization-Ledger.md wiki/Axiom-Catalog.md LeaTTa.wiki/
cd LeaTTa.wiki && git add -A && git commit -m "Sync wiki pages" && git push
```
