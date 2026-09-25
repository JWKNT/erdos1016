#!/usr/bin/env python3
"""Build every proof module and record the checked final statements and axioms."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from check_axiom_log import axiom_reports, check
from project_inventory import ROOT, inventory


def fingerprint(root: Path) -> str:
    """Bind evidence to the proof, audit, dependency pins, and verifier itself."""
    paths = [root / 'Erdos1016.lean', root / 'lakefile.lean',
             root / 'lake-manifest.json', root / 'lean-toolchain']
    for folder, pattern in [('Erdos1016', '*.lean'), ('audits', '*.lean'),
                            ('scripts', '*.py'), ('.github', '*.yml')]:
        paths.extend((root / folder).rglob(pattern))
    paths.extend((root / 'scripts').glob('*.sh'))
    manifest = ''.join(f'{p.relative_to(root).as_posix()} {hashlib.sha256(p.read_bytes()).hexdigest()}\n'
                       for p in sorted(set(paths)))
    return hashlib.sha256(manifest.encode()).hexdigest()


def structural_errors(report: dict) -> list[str]:
    errors = []
    if not report['all_sources_structural_checks_passed']:
        errors.append('Source screening failed; see inventory.json')
    if report['outside_umbrella_modules']:
        errors.append('Library modules outside the final theorem import closure')
    if report['duplicate_imports']:
        errors.append('Duplicate direct imports')
    if report['identical_source_groups']:
        errors.append('Identical source files')
    for name in report['modules']:
        if re.search(r'\bPaper\b|Section(?:One|Two|Three|Four|Five|Six|Seven|Eight|Nine|Ten|\d)|Scratch|Attempt|20\d{6}', name):
            errors.append('Non-descriptive module name: ' + name)
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fresh', action='store_true', help='rebuild all project modules from source')
    parser.add_argument('--jobs', type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    env = dict(os.environ, ELAN_TOOLCHAIN=(ROOT / 'lean-toolchain').read_text().strip())
    output = ROOT / '.verification'
    output.mkdir(exist_ok=True)
    initial_hash = fingerprint(ROOT)
    source = inventory(ROOT)
    (output / 'inventory.json').write_text(json.dumps(source, indent=2) + '\n')
    commit = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True, text=True)
    dirty = subprocess.run(['git', 'status', '--porcelain'], cwd=ROOT, capture_output=True, text=True)
    run_url = None
    if os.environ.get('GITHUB_RUN_ID'):
        run_url = (f"{os.environ.get('GITHUB_SERVER_URL', 'https://github.com')}/"
                   f"{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}")
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    result = {'schema_version': 1, 'status': 'running', 'fresh_project_build': args.fresh,
              'started_at': datetime.now(timezone.utc).isoformat(),
              'commit': commit.stdout.strip() if commit.returncode == 0 else None,
              'working_tree_clean': dirty.returncode == 0 and not dirty.stdout.strip(),
              'run_url': run_url, 'verification_input_sha256': initial_hash,
              'source_set_sha256': source['source_set_sha256'],
              'source_counts': source['counts']['all_library_sources'],
              'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
              'dependencies': {p['name']: p['rev'] for p in manifest['packages']},
              'checks': [], 'errors': []}
    destination = output / 'verification.json'

    def save() -> None:
        destination.write_text(json.dumps(result, indent=2) + '\n')

    def finish(errors: list[str]) -> int:
        if fingerprint(ROOT) != initial_hash:
            errors.append('Verification inputs changed while checking')
        result.update(status='failed' if errors else 'passed', errors=errors,
                      completed_at=datetime.now(timezone.utc).isoformat())
        save()
        print('\n'.join(errors) if errors else f'Verification passed: {destination}', flush=True)
        return 1 if errors else 0

    save()
    errors = structural_errors(source)
    if errors:
        return finish(errors)
    result['checks'].append('source_inventory')
    save()
    command = [sys.executable, 'scripts/rebuild.py', '--run', '--all', '--jobs', str(args.jobs)]
    if args.fresh:
        command.append('--fresh')
    code = subprocess.run(command, cwd=ROOT, env=env).returncode
    if code:
        return finish(['Lean rebuild or pinned environment preflight failed'])
    result['checks'].extend(['pinned_dependencies', 'all_library_modules_built'])
    save()
    log_path = output / 'main-theorem-audit.log'
    with log_path.open('w') as log:
        code = subprocess.run(['lake', 'env', 'lean', 'audits/MainTheoremAudit.lean'],
                              cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT).returncode
    text = log_path.read_text()
    errors = check(text)
    if code:
        errors.insert(0, f'Lean statement audit exited {code}')
    if errors:
        return finish(errors)
    result['axioms'] = axiom_reports(text)
    result['checks'].extend(['expanded_mathematical_statements', 'unconditional_endpoint_type',
                             'kernel_axiom_reports', 'verification_inputs_unchanged'])
    return finish([])


if __name__ == '__main__':
    raise SystemExit(main())
