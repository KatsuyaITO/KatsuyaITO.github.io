# Katsuya Ito Notes

個人の公開ノートをGitHub Pagesで配信するための、ビルド不要の静的サイトです。

## サイト構成

```text
scrapbox/
├── index.html    # ノート一覧、タグ、検索UI
├── initial-members-contractors.html # 初期メンバーと業務委託の記事
├── ai-native-document-server.html # AIネイティブなドキュメントサーバーの記事
├── software-industry-after-coding.html # コード生成後のソフトウェア産業の記事
├── ai-native-development-environment.html # AIネイティブな開発環境の記事
├── fundraising-and-good-company.html # 資金調達と100人の良い会社の記事
├── foundation-model-valuation.html # 生成AIファウンデーションモデル企業の企業価値の記事
├── hiring-a-french-engineer.html # フランス人エンジニアの採用と初期組織の記事
├── ultra-soul-new-business.html # 大企業の新規事業をB'zの例えで解く記事
├── app.js        # 検索、タグ絞り込み、並び替え
├── styles.css    # 一覧・記事・レスポンシブ表示
├── og/           # SNS共有用のOG画像（1200x630 PNG、記事ごとに1枚）
├── tools/
│   └── og-image.py # OG画像を記事HTMLから生成するスクリプト
└── readme.md     # この説明書
```

HTML、CSS、JavaScriptだけで動作します。Node.jsや静的サイトジェネレーターによるビルドは不要です。

## ローカルで確認する

リポジトリのルートで次を実行します。

```bash
python3 -m http.server 8765
```

ブラウザで次のURLを開きます。

```text
http://127.0.0.1:8765/scrapbox/
```

終了するときは、サーバーを実行しているターミナルで `Ctrl+C` を押します。

## 新しい記事を追加する

1. 既存の記事HTMLを複製して、記事用のHTMLファイルを作ります。
2. `<title>`、説明文、見出し、本文、日付、タグを変更します。
3. `index.html` の `.note-grid` 内に記事カードを追加します。
4. OG画像を生成します（`python3 tools/og-image.py new-article.html`）。
5. `<head>` のOG・Twitter Cardメタタグを新しい記事の内容に合わせます。

記事カードの例です。

```html
<a
  class="note-card"
  href="new-article.html"
  data-search-page="new-article.html"
  data-title="記事のタイトル"
  data-summary="記事の短い説明"
  data-tags="AI Product"
  data-date="2026-08-11"
>
  <div class="thumb thumb--map" aria-hidden="true"></div>
  <div class="card-body">
    <div class="card-meta">
      <span class="card-tag">AI</span>
      <time datetime="2026-08-11">2026.08.11</time>
    </div>
    <h2>記事のタイトル</h2>
    <p>記事の短い説明</p>
  </div>
</a>
```

`data-tags` には、半角スペース区切りで複数のタグを指定できます。

## OG・Twitter Cardメタデータ

SlackやXでURLを貼ったときのリンクプレビューを、全ページの `<head>` で指定しています。

- `og:type` / `og:title` / `og:description` / `og:url` / `og:site_name` / `og:locale`
- `og:image` と `og:image:width` `og:image:height`（1200x630）、`og:image:alt`
- `twitter:card`（`summary_large_image`）と `twitter:title` / `twitter:description` / `twitter:image`
- `link rel="canonical"`、`article:published_time`、`article:tag`
- JSON-LD構造化データ（一覧は `Blog`、記事は `BlogPosting`）

URLは `https://katsuyaito.github.io/scrapbox/` 起点の絶対URLで書きます。SlackとXは相対URLを解決しないため、ここを相対パスにするとプレビュー画像が出ません。

### OG画像を生成する

画像は記事HTMLの `<h1>`、タグ、日付、ノート番号を読み取って生成します。

```bash
python3 tools/og-image.py                    # 全記事を再生成
python3 tools/og-image.py new-article.html   # 1記事だけ生成
```

レンダリングにはインストール済みのGoogle Chromeをヘッドレスで使います。出力先は `og/<記事のファイル名>.png` です。

記事のタイトルを変更したときは、画像も再生成します。SlackとXはプレビューをキャッシュするため、公開後に画像を差し替えた場合は反映まで時間がかかります。

## 全文検索の仕組み

検索はブラウザ上のJavaScriptだけで動作します。

- タイトル: `data-title`
- 概要: `data-summary`
- タグ: `data-tags`
- 記事本文: `data-search-page` で指定したHTML

ページ表示時に `app.js` が同一サイト内の記事HTMLを取得し、`.article-content`、`article`、または `main` の本文を検索対象に追加します。

新しい記事を全文検索へ含めるには、一覧カードへ次の属性を付けます。

```html
data-search-page="new-article.html"
```

記事を取得できない場合でも、タイトル・概要・タグの検索は利用できます。

## タグを追加・変更する

`index.html` の `.tags` 内にフィルターボタンを追加します。

```html
<button class="tag" type="button" data-tag="Design">
  Design <span>3</span>
</button>
```

`data-tag` の値は、カード側の `data-tags` と完全に一致させます。`span` 内の件数は自動計算ではないため、記事を追加したときに更新します。

## サムネイルを変更する

現在のサムネイルは画像ファイルではなく、`styles.css` のCSSで描画しています。カードの `thumb--...` クラスを変更すると別のデザインを利用できます。

実画像を使用する場合は、画像を `scrapbox/images/` などへ保存し、次のように記述します。

```html
<div class="thumb">
  <img src="images/example.webp" alt="記事内容を表す説明">
</div>
```

画像はWebP形式を推奨し、表示速度のためにファイルサイズを小さくします。

## GitHub Pagesで公開する

このリポジトリでGitHub Pagesが有効になっていれば、変更をコミットして既定の公開ブランチへ反映すると、`/scrapbox/` 以下に公開されます。

公開前に次を確認します。

- メールアドレス、電話番号、住所などの個人情報が含まれていないか
- APIキー、トークン、Cookie、社内URLが含まれていないか
- 顧客名、契約情報、未公開の数値が含まれていないか
- 画像、引用、文章を公開する権利があるか
- 事実と個人的な仮説が区別されているか

## 現在の制約

- SNSプレビューの投稿者表示（`twitter:site` / `twitter:creator`）は、アカウントを指定していないため未設定です。
- 完成している記事ページは `initial-members-contractors.html`、`ai-native-document-server.html`、`software-industry-after-coding.html`、`ai-native-development-environment.html`、`fundraising-and-good-company.html`、`foundation-model-valuation.html`、`hiring-a-french-engineer.html`、`ultra-soul-new-business.html` の8件です。
- 検索インデックスはブラウザで作るため、記事数が非常に多くなった場合はJSON形式の検索インデックスを事前生成する構成への移行を検討します。
