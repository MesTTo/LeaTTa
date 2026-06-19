# Wiki source

These pages mirror the project's GitHub wiki. They are kept here so the content is
version-controlled and reviewable alongside the code.

- `Home.md` is the wiki landing page. It points readers to the documentation.
- `Developer-Guide.md` recommends the Lean toolchain, libraries, and proof machinery for
  contributors.

## Publishing to the GitHub wiki

GitHub creates the wiki git repository only after the first page is made in the browser.
One time, open `https://github.com/MesTTo/LeaTTa/wiki`, click "Create the first page",
and save. After that, publish these pages with:

```bash
git clone https://github.com/MesTTo/LeaTTa.wiki.git
cp wiki/Home.md wiki/Developer-Guide.md LeaTTa.wiki/
cd LeaTTa.wiki && git add -A && git commit -m "Sync wiki pages" && git push
```
