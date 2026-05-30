# Kalton--Roberts sub-19.838 bound API

This is a static Markdown rendering of `kalton_api_demo.ipynb`.
It is included so the demo remains readable on GitHub during notebook-renderer outages.

The notebook imports the local `kalton_api.py` module directly. No package installation is required.

```python
from pathlib import Path
import sys

root = Path.cwd()
if not (root / 'kalton_api.py').exists():
    root = root.parent
sys.path.insert(0, str(root))

import kalton_api as kr
root
```

## Run the exact verification

The verification uses only rational arithmetic for the logarithm intervals and exact `Fraction` arithmetic for the final constants.

```python
result = kr.run_all_checks(verbose=True)
```

## Main constants

```python
for row in kr.summary_table():
    print(f"{row['quantity']:>10}: {row['exact']}  =  {row['decimal']}")
```

## Programmatic access

The API returns dictionaries containing the exact constants and expander certificates, so other notebooks can reuse them without parsing the paper.

```python
constants = kr.case_constants()
expanders = kr.verify_expanders(verbose=False)
constants['Cmax'], [(e['name'], e['alpha'], e['theta']) for e in expanders]
```
