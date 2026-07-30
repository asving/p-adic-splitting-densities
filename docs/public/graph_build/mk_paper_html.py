#!/usr/bin/env python3
"""Convert paper_final.md (restricted markdown) to a site-styled HTML page."""
import re, html, pathlib

src = pathlib.Path('/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/public/paper_final.md').read_text()

def inline(s):
    s = html.escape(s, quote=False)
    s = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', s)
    s = re.sub(r'(?<!\*)\*([^*]+?)\*(?!\*)', r'<em>\1</em>', s)
    s = re.sub(r'arXiv:(\d{4}\.\d{4,5})', r'<a href="https://arxiv.org/abs/\1">arXiv:\1</a>', s)
    return s

lines = src.split('\n')
out = []
i = 0
first_h1 = True
while i < len(lines):
    ln = lines[i]
    if ln.startswith('# ') and first_h1:
        out.append('<h1>%s</h1>' % inline(ln[2:]))
        first_h1 = False
    elif ln.startswith('## '):
        out.append('<h2>%s</h2>' % inline(ln[3:]))
    elif ln.startswith('### '):
        out.append('<h3>%s</h3>' % inline(ln[4:]))
    elif ln.startswith('|'):
        rows = []
        while i < len(lines) and lines[i].startswith('|'):
            cells = [c.strip() for c in lines[i].strip().strip('|').split('|')]
            if not all(re.fullmatch(r'-+', c) for c in cells):
                rows.append(cells)
            i += 1
        i -= 1
        out.append('<table class="ledger"><thead><tr>' +
                   ''.join('<th>%s</th>' % inline(c) for c in rows[0]) + '</tr></thead><tbody>')
        for r in rows[1:]:
            out.append('<tr>' + ''.join('<td>%s</td>' % inline(c) for c in r) + '</tr>')
        out.append('</tbody></table>')
    elif ln.startswith('- '):
        items = []
        while i < len(lines) and lines[i].startswith('- '):
            items.append(lines[i][2:])
            i += 1
        i -= 1
        out.append('<ul>' + ''.join('<li>%s</li>' % inline(it) for it in items) + '</ul>')
    elif ln.strip() == '---':
        out.append('<hr>')
    elif ln.strip() == '':
        pass
    else:
        para = [ln]
        while i + 1 < len(lines) and lines[i+1].strip() != '' and not re.match(r'^(#|\||- |---)', lines[i+1]):
            i += 1
            para.append(lines[i])
        out.append('<p>%s</p>' % inline(' '.join(para)))
    i += 1

body = '\n'.join(out)

page = '''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>One Function for Every Prime - Asvin G</title>
    <link rel="stylesheet" href="../css/style.css">
    <style>
    .paper h1 { margin-bottom: 0.2em; }
    .paper h2 { margin-top: 1.4em; }
    .paper p { line-height: 1.55; }
    table.ledger { border-collapse: collapse; margin: 1em 0; font-size: 0.95rem; }
    table.ledger th, table.ledger td { border: 1px solid #bbb; padding: 0.45em 0.7em; vertical-align: top; text-align: left; }
    table.ledger th { background: #f0f0f0; }
    table.ledger td:first-child { max-width: 24em; }
    </style>
</head>
<body>
    <header>
        <img src="../images/banner.jpg" alt="Grothendieck-Riemann-Roch" class="banner">
        <div class="container">
            <div class="site-title">
                <h1><a href="../index.html">Asvin G</a></h1>
                <p class="tagline">Wir m&uuml;ssen wissen, wir werden wissen</p>
            </div>
            <nav><ul>
                <li><a href="../index.html">About</a></li>
                <li><a href="../blog.html">Blog</a></li>
                <li><a href="../claude/index.html">Claude</a></li>
                <li><a href="../book-reviews.html">Book Reviews</a></li>
            </ul></nav>
        </div>
    </header>
    <main class="container-narrow paper">
    <p class="post-date">July 2026 &mdash; companion to <a href="index.html">the expandable map of the formal development</a>.</p>
''' + body + '''
    </main>
    <footer><div class="container"><p>&copy; Asvin G &mdash; this page &copy; its author, such as that is</p></div></footer>
</body>
</html>
'''

dest = pathlib.Path('/tmp/graph_build/paper.html')
dest.write_text(page)
print('wrote', dest, len(page), 'bytes')
