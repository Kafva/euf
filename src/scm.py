import sys, re, os, traceback
from clang import cindex
from git.objects.commit import Commit
from git.repo.base import Repo
from git.exc import GitCommandError

from src import ERR_EXIT
from src.arg_states import matches_excluded
from src.config import CONFIG
from src.types import SourceDiff, SourceFile
from src.util import has_allowed_suffix, print_info

def filter_out_excluded(items: list, path_arr: list[str]) -> list:
    '''
    Filter out any files that are in excluded paths
    The paths are provided as python regex
    '''
    filtered = []

    for item,path in zip(items,path_arr):
        if not matches_excluded(path):
            filtered.append(item)

    return filtered

def get_source_diffs(commit_old: Commit, commit_new: Commit) -> list[SourceDiff]:
    COMMIT_DIFF = filter(lambda d: \
                has_allowed_suffix(d.a_path) and \
                re.match("M|R", d.change_type),
            commit_old.diff(commit_new) # type: ignore
    )

    return [ SourceDiff(new_path = d.b_path, old_path = d.a_path) \
            for d in COMMIT_DIFF ]

def get_commits(dep_repo: Repo) -> tuple[Commit,Commit]:
    commit_old: Commit = None # type: ignore
    commit_new: Commit = None # type: ignore

    for commit in dep_repo.iter_commits():
        if commit.hexsha.startswith(CONFIG.COMMIT_NEW):
            commit_new: Commit = commit
        elif commit.hexsha.startswith(CONFIG.COMMIT_OLD):
            commit_old: Commit = commit

    if not commit_old:
        print(f"Unable to find old commit: {CONFIG.COMMIT_OLD}")
        sys.exit(ERR_EXIT)
    if not commit_new:
        print(f"Unable to find new commit: {CONFIG.COMMIT_NEW}")
        sys.exit(ERR_EXIT)

    return (commit_old,commit_new)

def create_worktree(target: str, commit: str, repo: Repo) -> bool:
    if not os.path.exists(target):
        print_info(f"Creating worktree at {target}")
        # git checkout COMMIT_NEW.hexsha
        # git checkout -b euf-abcdefghi
        # git worktree add -b euf-abcdefghi /tmp/openssl euf-abcdefghi
        try:
            repo.git.worktree("add", "-b", f"euf-{commit[:8]}", target, commit) # type: ignore
        except GitCommandError:
            traceback.print_exc()
            return False
    return True

def get_source_files(path: str, ccdb: cindex.CompilationDatabase) -> list[SourceFile]:
    repo = Repo(path)
    source_files = filter(lambda p: has_allowed_suffix(p),
        [ e.path for e in repo.tree().traverse() ] # type: ignore
    )

    source_files = []
    for e in repo.tree().traverse(): # type: ignore
        if has_allowed_suffix(e.path):
            source_files.append(
                SourceFile.new(e.path,ccdb,path)
            )

    path_arr = [ s.new_path for s in source_files ]
    return filter_out_excluded(source_files, path_arr)

