"""Entry shim: the service lives in server.py.

Hosting sandboxes default to `python main.py`, so this file just starts the
real application with __main__ semantics (PORT binding included).
"""
import os
import runpy

runpy.run_path(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), 'server.py'),
    run_name='__main__',
)
