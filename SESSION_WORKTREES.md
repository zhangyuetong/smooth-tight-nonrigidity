# Fresh ver503 sessions

Each session uses the assigned publication-repository worktree and branch from COORDINATION.md. Old checkouts remain read-only provenance sources. The coordinator validates and commits the reconciled checkpoint before creating workers from that exact commit.

From an assigned worktree's `lean` directory:

```powershell
. ./scripts/worktree-environment.ps1
python scripts/build.py --module TightVer401.YourOwnedModule --jobs 1
python scripts/verify.py --jobs 1
python scripts/build_blueprint.py
```

Shared pinned Mathlib packages are read-only. Set VER401_PACKAGES or supply -Packages if automatic discovery fails. The setup adds process-local Git trust and confirms exact Mathlib revision. Portable publication builder/compiler discovery stays intact.

Optional private cache seeding (empty local outputs only):

```powershell
. ./scripts/worktree-environment.ps1 -SeedCache -SeedEngine C:/Users/gzhan/Documents/ChatGPT/tight_another_review/ver503-integration/lean
```

Copies are private; exact current source, compatibility-source, dependency, object and log hashes must pass the builder/full verifier. A copied audit alone is insufficient. Each parent is sole compiler writer; subagents may edit exclusive source leaves or review read-only, never compile. No bulk logs/caches/binaries are committed. Workers leave frozen source commits, exact consumers, same-object facts, remaining holes and audit/source hashes.
