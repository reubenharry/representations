# Agent notes — representations

Standalone library extracted from `quantum`. Same hard bans as that repo:

1. No basis-sum in production.
2. No new `unsafeCoerce` without explicit user approval.
3. No temporary hacks; honest `undefined` beats a lie that typechecks.

Verify with:

```bash
cabal build representations:lib:representations
```

Depends on a sibling checkout of `linearmap-family` (see `cabal.project`).
Schur intertwiners live in `Representations.Intertwiner`; the forgetful category is `Representations.Mor`.
