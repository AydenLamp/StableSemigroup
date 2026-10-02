# StableSemigroup

This repository uses a simple branch model:

- `main`: the refactored code you actively develop.
- `legacy` (or another name you choose): old code snapshot, mostly read-only reference.

No pull-request workflow is required for normal development in this repo.

## What Branches Are (Quick Explanation)

A branch is a named line of commit history.

- Think of `main` as your primary working timeline.
- `legacy` is a separate timeline used to preserve old code.
- Switching branches changes which timeline your working folder is showing.

Useful commands:

```bash
git branch
```

Shows all local branches and marks your current branch with `*`.

```bash
git checkout main
```

Switches to `main`.

```bash
git checkout legacy
```

Switches to `legacy`.

```bash
git switch main
```

Modern equivalent of `git checkout main`.

Before switching, commit or stash your work so uncommitted changes do not block the switch.

## Branch Model

### `main`

Use `main` for all day-to-day coding.

- You and your collaborator both commit directly to `main`.
- Keep commits small and descriptive.
- Pull before you start work to avoid conflicts.

### `legacy`

Use `legacy` to preserve the old code.

- Treat it like an archive branch.
- Avoid committing to it unless you intentionally refresh the snapshot.

### Optional review branches

If you want to park or compare alternative code ideas, create temporary branches and keep them separate from `main`.

## Create the Legacy Branch

If you have not created the old-code branch yet:

```bash
git checkout -b legacy
git push -u origin legacy
git checkout main
```

## Daily Workflow (Direct Commits to `main`)

1. Move to `main` and pull latest changes:

```bash
git checkout main
git pull
```

2. Make edits.

3. Verify Lean builds:

```bash
lake build
```

4. Commit and push:

```bash
git add .
git commit -m "Short clear description of the change"
git push
```

## What to Do When Pull Fails

If both people changed the same file, `git pull` may report a conflict.

Basic conflict workflow:

1. Run `git status` to see conflicted files.
2. Edit files and keep the correct final content.
3. Mark resolved files with `git add <file>`.
4. Finish with `git commit`.
5. Push with `git push`.

## About GitHub Workflows

This repository previously had GitHub Actions workflows for CI, release tags, and dependency updates.

If you delete those workflow files, GitHub will stop running that automation.
That is totally valid for a simple direct-to-main process.