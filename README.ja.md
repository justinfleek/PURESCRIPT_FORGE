<p align="center">
  <a href="https://forge.ai">
    <picture>
      <source srcset="packages/console/app/src/asset/logo-ornate-dark.svg" media="(prefers-color-scheme: dark)">
      <source srcset="packages/console/app/src/asset/logo-ornate-light.svg" media="(prefers-color-scheme: light)">
      <img src="packages/console/app/src/asset/logo-ornate-light.svg" alt="Forge logo">
    </picture>
  </a>
</p>
<p align="center">オープンソースのAIコーディングエージェント。</p>
<p align="center">
  <a href="https://forge.ai/discord"><img alt="Discord" src="https://img.shields.io/discord/1391832426048651334?style=flat-square&label=discord" /></a>
  <a href="https://www.npmjs.com/package/forge-ai"><img alt="npm" src="https://img.shields.io/npm/v/forge-ai?style=flat-square" /></a>
  <a href="https://github.com/forge-ai/forge/actions/workflows/publish.yml"><img alt="Build status" src="https://img.shields.io/github/actions/workflow/status/forge-ai/forge/publish.yml?style=flat-square&branch=dev" /></a>
</p>

<p align="center">
  <a href="README.md">English</a> |
  <a href="README.zh.md">简体中文</a> |
  <a href="README.zht.md">繁體中文</a> |
  <a href="README.ko.md">한국어</a> |
  <a href="README.de.md">Deutsch</a> |
  <a href="README.es.md">Español</a> |
  <a href="README.fr.md">Français</a> |
  <a href="README.it.md">Italiano</a> |
  <a href="README.da.md">Dansk</a> |
  <a href="README.ja.md">日本語</a> |
  <a href="README.pl.md">Polski</a> |
  <a href="README.ru.md">Русский</a> |
  <a href="README.ar.md">العربية</a> |
  <a href="README.no.md">Norsk</a> |
  <a href="README.br.md">Português (Brasil)</a>
</p>

[![Forge Terminal UI](packages/web/src/assets/lander/screenshot.png)](https://forge.ai)

---

### インストール

```bash
# YOLO
curl -fsSL https://forge.ai/install | bash

# パッケージマネージャー
npm i -g forge-ai@latest        # bun/pnpm/yarn でもOK
scoop install forge             # Windows
choco install forge             # Windows
brew install forge-ai/tap/forge # macOS と Linux（推奨。常に最新）
brew install forge              # macOS と Linux（公式 brew formula。更新頻度は低め）
paru -S forge-bin               # Arch Linux
mise use -g forge               # どのOSでも
nix run nixpkgs#forge           # または github:forge-ai/forge で最新 dev ブランチ
```

> [!TIP]
> インストール前に 0.1.x より古いバージョンを削除してください。

### デスクトップアプリ (BETA)

Forge はデスクトップアプリとしても利用できます。[releases page](https://github.com/forge-ai/forge/releases) から直接ダウンロードするか、[forge.ai/download](https://forge.ai/download) を利用してください。

| プラットフォーム      | ダウンロード                          |
| --------------------- | ------------------------------------- |
| macOS (Apple Silicon) | `forge-desktop-darwin-aarch64.dmg` |
| macOS (Intel)         | `forge-desktop-darwin-x64.dmg`     |
| Windows               | `forge-desktop-windows-x64.exe`    |
| Linux                 | `.deb`、`.rpm`、または AppImage       |

```bash
# macOS (Homebrew)
brew install --cask forge-desktop
# Windows (Scoop)
scoop bucket add extras; scoop install extras/forge-desktop
```

#### インストールディレクトリ

インストールスクリプトは、インストール先パスを次の優先順位で決定します。

1. `$FORGE_INSTALL_DIR` - カスタムのインストールディレクトリ
2. `$XDG_BIN_DIR` - XDG Base Directory Specification に準拠したパス
3. `$HOME/bin` - 標準のユーザー用バイナリディレクトリ（存在する場合、または作成できる場合）
4. `$HOME/.forge/bin` - デフォルトのフォールバック

```bash
# 例
FORGE_INSTALL_DIR=/usr/local/bin curl -fsSL https://forge.ai/install | bash
XDG_BIN_DIR=$HOME/.local/bin curl -fsSL https://forge.ai/install | bash
```

### Agents

Forge には組み込みの Agent が2つあり、`Tab` キーで切り替えられます。

- **build** - デフォルト。開発向けのフルアクセス Agent
- **plan** - 分析とコード探索向けの読み取り専用 Agent
  - デフォルトでファイル編集を拒否
  - bash コマンド実行前に確認
  - 未知のコードベース探索や変更計画に最適

また、複雑な検索やマルチステップのタスク向けに **general** サブ Agent も含まれています。
内部的に使用されており、メッセージで `@general` と入力して呼び出せます。

[agents](https://forge.ai/docs/agents) の詳細はこちら。

### ドキュメント

Forge の設定については [**ドキュメント**](https://forge.ai/docs) を参照してください。

### コントリビュート

Forge に貢献したい場合は、Pull Request を送る前に [contributing docs](./CONTRIBUTING.md) を読んでください。

### Forge の上に構築する

Forge に関連するプロジェクトで、名前に "forge"（例: "forge-dashboard" や "forge-mobile"）を含める場合は、そのプロジェクトが Forge チームによって作られたものではなく、いかなる形でも関係がないことを README に明記してください。

### FAQ

#### Claude Code との違いは？

機能面では Claude Code と非常に似ています。主な違いは次のとおりです。

- 100% オープンソース
- 特定のプロバイダーに依存しません。[Forge Core](https://forge.ai/core) で提供しているモデルを推奨しますが、Forge は Claude、OpenAI、Google、またはローカルモデルでも利用できます。モデルが進化すると差は縮まり価格も下がるため、provider-agnostic であることが重要です。
- そのまま使える LSP サポート
- TUI にフォーカス。Forge は neovim ユーザーと [terminal.shop](https://terminal.shop) の制作者によって作られており、ターミナルで可能なことの限界を押し広げます。
- クライアント/サーバー構成。例えば Forge をあなたのPCで動かし、モバイルアプリからリモート操作できます。TUI フロントエンドは複数あるクライアントの1つにすぎません。

---

**コミュニティに参加** [Discord](https://discord.gg/forge) | [X.com](https://x.com/forge)
