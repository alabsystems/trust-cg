from pathlib import Path
import subprocess, sys
# This child and its command stay inside the anchored guard's process group.
with Path(sys.argv[1]).open('wb') as log:
    result = subprocess.run(sys.argv[2:], stdout=log, stderr=subprocess.STDOUT)
sys.exit(result.returncode)
