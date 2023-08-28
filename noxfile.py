"""Nox sessions."""

from __future__ import annotations

import nox

nox.options.sessions = ["lint"]


@nox.session(reuse_venv=True)
def lint(session: nox.Session) -> None:
    """Lint the Python part of the codebase using pre-commit.

    Simply execute `nox -rs lint` to run all configured hooks.
    """
    session.install("pre-commit")
    session.run("pre-commit", "run", "--all-files", *session.posargs)
