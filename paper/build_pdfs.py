#!/usr/bin/env python3
"""Build the English manuscript using a configured XeLaTeX installation.

Run from the repository root with ``python paper/build_pdfs.py``. Build files
remain in paper/_build; a successful PDF is copied into paper/. The optional
--minimal-tex flag enables a local-format workaround for minimal Debian TeX
installations. It is unnecessary for a normally configured distribution.

Proof verification requires only Python's standard library and is independent
of this optional typesetting step. Required fonts are listed in README.md.
"""
import argparse
from pathlib import Path
import os
import shutil
import subprocess

PAPER = Path(__file__).resolve().parent
BUILD = PAPER / '_build'
STEM = 'bernoulli4_manuscript'


def run(command, environment, workdir, logfile):
    result = subprocess.run(command, cwd=workdir, env=environment,
                            capture_output=True, text=True,
                            encoding='utf-8', errors='replace')
    output = result.stdout + result.stderr
    logfile.write_text(output, encoding='utf-8')
    if result.returncode:
        raise RuntimeError('Compilation failed; see ' + str(logfile) + '\n' +
                           output[-2500:])
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--minimal-tex', action='store_true',
                        help='build a local format for a minimal Debian TeX installation')
    args = parser.parse_args()
    xelatex = shutil.which('xelatex')
    if xelatex is None:
        raise SystemExit('XeLaTeX was not found. Install a configured XeLaTeX '
                         'distribution and the fonts listed in README.md.')
    BUILD.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    command = [xelatex]
    if args.minimal_tex:
        xetex = shutil.which('xetex')
        roots = [Path('/usr/share/texlive/texmf-dist'),
                 Path('/usr/share/texmf'), Path('/etc/texmf')]
        if xetex is None or not (roots[0] / 'tex/latex/base/latex.ltx').is_file():
            raise SystemExit('--minimal-tex requires xetex and the Debian TeX '
                             'tree at /usr/share/texlive/texmf-dist.')
        environment['TEXMF'] = '{' + ','.join(str(p) for p in roots if p.exists()) + '}'
        format_dir = BUILD / 'format'
        format_dir.mkdir(exist_ok=True)
        # Rebuild the workaround format to avoid reusing one from an older engine.
        run([xetex, '-ini', '-interaction=nonstopmode', '-halt-on-error',
             '-jobname=xelatex', '-etex', '-progname=xelatex', 'xelatex.ini'],
            environment, format_dir, BUILD / 'format-build.log')
        command.append('-fmt=' + str(format_dir / 'xelatex.fmt'))
    command.extend(['-interaction=nonstopmode', '-halt-on-error',
                    '-file-line-error', '-no-shell-escape',
                    '-output-directory=' + str(BUILD), STEM + '.tex'])
    built_pdf = BUILD / (STEM + '.pdf')
    if built_pdf.exists():
        built_pdf.unlink()
    for pass_number in (1, 2):
        log = run(command, environment, PAPER,
                  BUILD / (STEM + '-' + str(pass_number) + '.log'))
    if not built_pdf.is_file():
        raise RuntimeError('XeLaTeX finished without producing ' + str(built_pdf))
    destination = PAPER / (STEM + '.pdf')
    shutil.copy2(built_pdf, destination)
    print('Built paper/' + destination.name)
    for line in log.splitlines():
        if any(term in line for term in ('Warning:', 'Overfull', 'Missing character')):
            print('  ' + line)


if __name__ == '__main__':
    main()
