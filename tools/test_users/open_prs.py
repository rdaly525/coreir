#!/usr/bin/env python
import github3
from netrc import netrc

netrc = netrc('github.netrc')
login, _, password = netrc.authenticators('api.github.com')

g = github3.login(login, password)

coreir = g.repository("rdaly525", "coreir")
coreir_pr = [_ for _ in coreir.pull_requests(state="open", head="dev", base="master")][0]

for owner, repo, branch in [
    ("leonardt", "pycoreir", "dev"),
    ("phanrahan", "magma", "coreir-dev"),
    ("phanrahan", "mantle", "coreir-dev")
    ]:
    body = f"Tracking coreir PR {coreir_pr.html_url}"
    title = f"Tracking rdaly525 PR {coreir_pr.number}"
    print(f"Creating PR for {owner}/{repo}:{branch} with title=\"{title}\" body=\"{body}\"")
    try:
        result = g.repository(owner, repo).create_pull(title=title, base="master", head=branch, body=body)
        print(result)
    except github3.exceptions.UnprocessableEntity as e:
        print(f"Caught exception: {e}")
        print("Could be that there are no changes between dev branch and master")
        print("FIXME: Should check that there are any changes to pull")
