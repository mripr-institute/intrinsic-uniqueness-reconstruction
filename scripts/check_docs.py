#!/usr/bin/env python3
"""Check repository-local Markdown navigation and maintained audit-map paths.

External URLs are not fetched. Historical JSON paths are frozen provenance,
not runnable links; the separate historical graph checker resolves its register.
"""

import html
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED = {'.git', '.lake', '.venv', '__pycache__'}


def prose(text):
    lines = []
    fence = None
    for line in text.splitlines():
        match = re.match(r'^\s*(`{3,}|~{3,})', line)
        if match:
            marker = match.group(1)
            if fence is None:
                fence = marker
            elif marker[0] == fence[0] and len(marker) >= len(fence):
                fence = None
            lines.append('')
        else:
            lines.append('' if fence else line)
    return '\n'.join(lines)


def anchors(text):
    seen, result = {}, set()
    for heading in re.findall(r'^ {0,3}#{1,6}\s+(.+?)\s*#*$', prose(text), re.M):
        heading = re.sub(r'<[^>]+>', '', heading)
        heading = re.sub(r'\[([^\]]+)\]\([^)]*\)', r'\1', heading)
        slug = re.sub(r'[^\w\- ]', '', html.unescape(heading).lower()).replace(' ', '-')
        count = seen.get(slug, 0)
        result.add(slug + (f'-{count}' if count else ''))
        seen[slug] = count + 1
    result.update(re.findall(r'<a\s+(?:name|id)=[\"\']([^\"\']+)', text))
    return result


def main():
    errors, checked = [], 0
    documents = sorted(p for p in ROOT.rglob('*.md') if not EXCLUDED.intersection(p.parts))
    for path in documents:
        text = prose(path.read_text())
        # Code spans are not links; preserve backtick-marked link captions.
        text = re.sub(r'(`+)(?!`).*?\1', '', text)
        # Plain-text coefficient extraction in historical mathematics is not
        # navigation: for example [zⁿ](1−z)^(-k−1).
        text = re.sub(r'\[[A-Za-z][⁰¹²³⁴⁵⁶⁷⁸⁹ⁿ]+\]\([^\n)]+\)\^', '', text)
        destinations = re.findall(r'!?\[[^\[\]\n]*\]\(<?([^\s)>]+)>?(?:\s+[\"\'][^\n]*[\"\'])?\)', text)
        definitions = {k.strip().lower(): v for k, v in re.findall(
            r'^ {0,3}\[([^\]]+)\]:\s*<?([^\s>]+)>?', text, re.M)}
        for caption, reference in re.findall(r'\[([^\[\]\n]+)\]\[([^\]\n]*)\]', text):
            key = (reference or caption).strip().lower()
            if key not in definitions:
                errors.append(f'{path.relative_to(ROOT)}: undefined reference [{key}]')
        destinations.extend(definitions.values())
        for target in destinations:
            parsed = urlsplit(target)
            if parsed.scheme or parsed.netloc:
                continue
            checked += 1
            file = (ROOT / unquote(parsed.path.lstrip('/')) if parsed.path.startswith('/')
                    else path.parent / unquote(parsed.path)) if parsed.path else path
            file = file.resolve()
            label = f'{path.relative_to(ROOT)}: {target}'
            if not file.exists():
                errors.append(label + ' (missing file)')
                continue
            fragment = unquote(parsed.fragment)
            if not fragment:
                continue
            line = re.fullmatch(r'L(\d+)(?:-L(\d+))?', fragment)
            if line and file.is_file():
                first, last = int(line[1]), int(line[2] or line[1])
                if not 1 <= first <= last <= len(file.read_text().splitlines()):
                    errors.append(label + ' (invalid line anchor)')
            elif file.suffix == '.md' and fragment not in anchors(file.read_text()):
                errors.append(label + ' (missing heading anchor)')

    for path in sorted((ROOT / 'audits/maps').glob('*.json')):
        data = json.loads(path.read_text())
        def strings(value):
            if isinstance(value, str):
                yield value
            elif isinstance(value, dict):
                for child in value.values():
                    yield from strings(child)
            elif isinstance(value, list):
                for child in value:
                    yield from strings(child)
        for value in strings(data):
            for ref in re.findall(r'(?:\.\./history/|audits/|paper/|lean/)[\w./-]+\.(?:md|json|tex|lean)\b', value):
                file = path.parent / ref if ref.startswith('../') else ROOT / ref
                if not file.exists():
                    errors.append(f'{path.relative_to(ROOT)}: {ref} (missing map reference)')
    if errors:
        raise SystemExit('\n'.join(sorted(set(errors))))
    print(f'Documentation: PASS; {len(documents)} Markdown files, {checked} local links; '
          'heading/line anchors and maintained map references checked.')


if __name__ == '__main__':
    main()
