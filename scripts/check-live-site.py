#!/usr/bin/env python3
"""Check the deployed site against the commit that built it.

The publishing run deploys inside the docgen action, after which nothing reads
the result: the default edition is built there and the checks of
``check-web-build.py`` never see it. This check reads the site itself. It takes
the site's base URL and the short hash of the commit the run built from, waits
until the home page carries that commit's stamp (``blueprint/src/buildstamp.tex``
and ``home_page/index.md``, written by the workflow), then fetches the
dependency graph and the gather section of each web edition into a temporary
directory and applies ``check-web-build.py`` to them, and asserts that the PDF
and the API documentation answer. The gather section is named by its label, so
its page name is stable, and its nodes carry the Lean links the check counts.

Usage: python3 scripts/check-live-site.py <base-url> <sha7> [--wait SECONDS]

The wait for the stamp is ten minutes unless ``--wait`` says otherwise; every
other check runs whether or not the stamp appeared, so one run reports
everything. Exits 0 when every check passes, else lists the failures and exits 1.
"""

import importlib.util
import re
import sys
import tempfile
import time
import urllib.error
import urllib.request
from pathlib import Path

EDITIONS = ("blueprint", "blueprint-full")
PAGES = ("dep_graph_document.html", "sec-aba-gather.html")
ANSWERING = ("blueprint.pdf", "docs/index.html")
POLL_SECONDS = 30


def fetch(url: str) -> tuple[int, bytes]:
    """GET the URL; return the status and the body, a failed request as (0, b'')."""
    request = urllib.request.Request(url, headers={"User-Agent": "check-live-site"})
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            return response.status, response.read()
    except urllib.error.HTTPError as error:
        return error.code, b""
    except (urllib.error.URLError, TimeoutError, OSError):
        return 0, b""


def web_build_check():
    """The main function of check-web-build.py, loaded from its hyphenated file."""
    path = Path(__file__).with_name("check-web-build.py")
    spec = importlib.util.spec_from_file_location("check_web_build", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.main


def wait_for_stamp(base: str, sha: str, wait: float) -> str | None:
    """Poll the home page until it carries the stamp; return a failure or None.

    Jekyll renders the stamp's commit as a link, so the tags are stripped
    before the search.
    """
    stamp = f"Built from commit {sha}"
    deadline = time.monotonic() + wait
    attempt = 0
    while True:
        attempt += 1
        status, body = fetch(f"{base}/")
        text = re.sub(r"<[^>]+>", "", body.decode("utf-8", errors="replace"))
        if status == 200 and stamp in text:
            print(f"home page: carries the stamp of {sha} (attempt {attempt})")
            return None
        if time.monotonic() >= deadline:
            seen = "no stamp" if "Built from commit" not in text else "another commit's stamp"
            return (
                f"{base}/ answered {status} with {seen} after {attempt} attempts "
                f"over {int(wait)} s; the deployment of {sha} did not reach the site"
            )
        time.sleep(min(POLL_SECONDS, max(0.0, deadline - time.monotonic())))


def main(argv: list[str]) -> int:
    args = list(argv[1:])
    wait = 600.0
    if "--wait" in args:
        at = args.index("--wait")
        try:
            wait = float(args[at + 1])
        except (IndexError, ValueError):
            print(f"usage: {argv[0]} <base-url> <sha7> [--wait SECONDS]", file=sys.stderr)
            return 2
        del args[at : at + 2]
    if len(args) != 2:
        print(f"usage: {argv[0]} <base-url> <sha7> [--wait SECONDS]", file=sys.stderr)
        return 2
    base, sha = args[0].rstrip("/"), args[1]
    failures = []

    failure = wait_for_stamp(base, sha, wait)
    if failure:
        failures.append(failure)

    check = web_build_check()
    with tempfile.TemporaryDirectory() as temporary:
        for edition in EDITIONS:
            directory = Path(temporary) / edition
            directory.mkdir()
            missing = []
            for page in PAGES:
                status, body = fetch(f"{base}/{edition}/{page}")
                if status != 200:
                    missing.append(f"{edition}/{page} answered {status}")
                    continue
                (directory / page).write_bytes(body)
            if missing:
                failures.extend(missing)
                continue
            print(f"edition {edition}:")
            if check([argv[0], str(directory)]) != 0:
                failures.append(f"{edition}: the deployed pages fail check-web-build.py")

    for path in ANSWERING:
        status, _ = fetch(f"{base}/{path}")
        print(f"{path}: {status}")
        if status != 200:
            failures.append(f"{base}/{path} answered {status}")

    sys.stdout.flush()
    for failure in failures:
        print(f"error: {failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
