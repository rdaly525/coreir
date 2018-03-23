Create a `github.netrc` file in this directory with the contents
```
machine api.github.com
login <github_username>
password <github_password>
```

Install the Python dependencies
```
pip install github3.py
```

Run the following command in a directory that contains the following repositories:
`coreir`, `pycoreir`, `magma`, `mantle`.
```
❯ ls
...
coreir
pycoreir
magma
mantle
...
❯ ./coreir/tools/test_users/run_tests.sh
```

If the tests pass, open pull requests using `python open_prs.py`
