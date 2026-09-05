#!/usr/bin/env python3
"""記事HTMLからOG画像（1200x630 PNG）を生成する。

  python3 tools/og-image.py               # 全記事を再生成
  python3 tools/og-image.py new-note.html # 1記事だけ生成

見出し・タグ・日付・ノート番号は記事HTMLから読み取るため、引数以外の設定は不要。
レンダリングにはインストール済みのGoogle Chrome（ヘッドレス）を使う。
"""
import html
import pathlib
import re
import subprocess
import sys
import tempfile

SB = pathlib.Path(__file__).resolve().parent.parent
OG = SB / "og"
CHROME = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"

CARD = """<!doctype html><html lang="ja"><head><meta charset="utf-8"><style>
*{{box-sizing:border-box;margin:0;padding:0}}
html,body{{width:1200px;height:630px}}
body{{background:#f4f7f8;font-family:"Avenir Next","Hiragino Kaku Gothic ProN","Yu Gothic",sans-serif;-webkit-font-smoothing:antialiased;color:#101820;display:flex;align-items:center;justify-content:center}}
.card{{position:relative;width:1078px;height:508px;background:#fff;border:1px solid #101820;box-shadow:16px 16px 0 #dce2e6;padding:56px 60px 48px;display:flex;flex-direction:column}}
.card::before{{content:"";position:absolute;left:-1px;right:-1px;top:-1px;height:10px;background:{accent}}}
.top{{display:flex;align-items:center;gap:16px}}
.mark{{width:52px;height:52px;border-radius:50%;background:#101820;color:#fff;display:flex;align-items:center;justify-content:center;font:700 17px/1 ui-monospace,SFMono-Regular,Menlo,monospace;letter-spacing:-.05em}}
.who strong{{display:block;font-size:20px;letter-spacing:-.02em}}
.who small{{display:block;margin-top:3px;color:#66717d;font:600 11px/1.2 ui-monospace,SFMono-Regular,Menlo,monospace;letter-spacing:.16em}}
h1{{margin:auto 0;font-size:{fs}px;line-height:1.5;letter-spacing:-.03em;font-weight:700}}
h1 em{{color:#2455f4;font-style:normal}}
.bottom{{display:flex;align-items:center;gap:14px;padding-top:26px;border-top:1px solid #dce2e6}}
.chip{{padding:8px 13px;background:#2455f4;color:#fff;font:700 12px/1 ui-monospace,SFMono-Regular,Menlo,monospace;letter-spacing:.11em}}
.date{{color:#66717d;font:600 13px/1 ui-monospace,SFMono-Regular,Menlo,monospace;letter-spacing:.08em}}
.host{{margin-left:auto;color:#66717d;font:600 13px/1 ui-monospace,SFMono-Regular,Menlo,monospace;letter-spacing:.06em}}
</style></head><body><div class="card">
<div class="top"><div class="mark">KI</div><div class="who"><strong>Katsuya Ito</strong><small>NOTES / {no}</small></div></div>
<h1>{h1}</h1>
<div class="bottom"><span class="chip">{tag}</span><span class="date">{date}</span><span class="host">katsuyaito.github.io/scrapbox</span></div>
</div></body></html>"""


def font_size(n):
    for limit, size in ((22, 62), (30, 54), (40, 46), (52, 40)):
        if n <= limit:
            return size
    return 35


def read_article(path):
    s = path.read_text(encoding="utf-8")
    home = path.name == "index.html"
    if home:
        h1 = re.search(r'<h1 id="page-title">(.*?)</h1>', s, re.S).group(1)
        tag, date = "OPEN NOTEBOOK", "2026-09-05"
    else:
        h1 = re.search(r"<h1>(.*?)</h1>", s, re.S).group(1)
        meta = re.search(r'<div class="article-meta"><span>(.*?)</span><time datetime="(.*?)"', s, re.S)
        tag, date = meta.group(1), meta.group(2)
    no = re.search(r"<small>Notes / (\d+)</small>", s).group(1)
    plain = html.unescape(re.sub(r"<[^>]+>", "", h1))
    return dict(h1=h1.strip(), tag=tag, date=date, no=no, length=len(plain), home=home)


def render(path):
    a = read_article(path)
    markup = CARD.format(
        accent="#9ef2dc" if a["home"] else "#ffdf66",
        fs=font_size(a["length"]),
        no=a["no"],
        h1=a["h1"],
        tag=html.escape(a["tag"].upper()),
        date=a["date"].replace("-", "."),
    )
    OG.mkdir(exist_ok=True)
    out = OG / f"{path.stem}.png"
    with tempfile.TemporaryDirectory() as tmp:
        card = pathlib.Path(tmp) / "card.html"
        card.write_text(markup, encoding="utf-8")
        subprocess.run(
            [CHROME, "--headless=new", "--disable-gpu", "--hide-scrollbars", "--no-sandbox",
             "--force-device-scale-factor=1", "--window-size=1200,630",
             f"--screenshot={out}", card.as_uri()],
            check=True, capture_output=True,
        )
    print(f"{out.relative_to(SB)}  ({out.stat().st_size:,} bytes)")


if __name__ == "__main__":
    targets = [SB / n for n in sys.argv[1:]] or sorted(SB.glob("*.html"))
    for t in targets:
        render(t)
