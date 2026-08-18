# Agent notes — symmetry

Standalone library extracted from `quantum`. Same hard bans as that repo:

1. No basis-sum in production.
2. No new `unsafeCoerce` without explicit user approval.
3. No temporary hacks; honest `undefined` beats a lie that typechecks.

Verify with:

```bash
cabal build symmetry:lib:symmetry
```

Depends on a sibling checkout of `linearmap-family` (see `cabal.project`).
