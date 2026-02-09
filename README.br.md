<p align="center">
  <a href="https://forge.ai">
    <picture>
      <source srcset="packages/console/app/src/asset/logo-ornate-dark.svg" media="(prefers-color-scheme: dark)">
      <source srcset="packages/console/app/src/asset/logo-ornate-light.svg" media="(prefers-color-scheme: light)">
      <img src="packages/console/app/src/asset/logo-ornate-light.svg" alt="Logo do Forge">
    </picture>
  </a>
</p>
<p align="center">O agente de programação com IA de código aberto.</p>
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

### Instalação

```bash
# YOLO
curl -fsSL https://forge.ai/install | bash

# Gerenciadores de pacotes
npm i -g forge-ai@latest        # ou bun/pnpm/yarn
scoop install forge             # Windows
choco install forge             # Windows
brew install forge-ai/tap/forge # macOS e Linux (recomendado, sempre atualizado)
brew install forge              # macOS e Linux (fórmula oficial do brew, atualiza menos)
paru -S forge-bin               # Arch Linux
mise use -g forge               # qualquer sistema
nix run nixpkgs#forge           # ou github:forge-ai/forge para a branch dev mais recente
```

> [!TIP]
> Remova versões anteriores a 0.1.x antes de instalar.

### App desktop (BETA)

O Forge também está disponível como aplicativo desktop. Baixe diretamente pela [página de releases](https://github.com/forge-ai/forge/releases) ou em [forge.ai/download](https://forge.ai/download).

| Plataforma            | Download                              |
| --------------------- | ------------------------------------- |
| macOS (Apple Silicon) | `forge-desktop-darwin-aarch64.dmg` |
| macOS (Intel)         | `forge-desktop-darwin-x64.dmg`     |
| Windows               | `forge-desktop-windows-x64.exe`    |
| Linux                 | `.deb`, `.rpm` ou AppImage            |

```bash
# macOS (Homebrew)
brew install --cask forge-desktop
# Windows (Scoop)
scoop bucket add extras; scoop install extras/forge-desktop
```

#### Diretório de instalação

O script de instalação respeita a seguinte ordem de prioridade para o caminho de instalação:

1. `$FORGE_INSTALL_DIR` - Diretório de instalação personalizado
2. `$XDG_BIN_DIR` - Caminho compatível com a especificação XDG Base Directory
3. `$HOME/bin` - Diretório binário padrão do usuário (se existir ou puder ser criado)
4. `$HOME/.forge/bin` - Fallback padrão

```bash
# Exemplos
FORGE_INSTALL_DIR=/usr/local/bin curl -fsSL https://forge.ai/install | bash
XDG_BIN_DIR=$HOME/.local/bin curl -fsSL https://forge.ai/install | bash
```

### Agents

O Forge inclui dois agents integrados, que você pode alternar com a tecla `Tab`.

- **build** - Padrão, agent com acesso total para trabalho de desenvolvimento
- **plan** - Agent somente leitura para análise e exploração de código
  - Nega edições de arquivos por padrão
  - Pede permissão antes de executar comandos bash
  - Ideal para explorar codebases desconhecidas ou planejar mudanças

Também há um subagent **general** para buscas complexas e tarefas em várias etapas.
Ele é usado internamente e pode ser invocado com `@general` nas mensagens.

Saiba mais sobre [agents](https://forge.ai/docs/agents).

### Documentação

Para mais informações sobre como configurar o Forge, [**veja nossa documentação**](https://forge.ai/docs).

### Contribuir

Se você tem interesse em contribuir com o Forge, leia os [contributing docs](./CONTRIBUTING.md) antes de enviar um pull request.

### Construindo com Forge

Se você estiver trabalhando em um projeto relacionado ao Forge e estiver usando "forge" como parte do nome (por exemplo, "forge-dashboard" ou "forge-mobile"), adicione uma nota no README para deixar claro que não foi construído pela equipe do Forge e não é afiliado a nós de nenhuma forma.

### FAQ

#### Como isso é diferente do Claude Code?

É muito parecido com o Claude Code em termos de capacidade. Aqui estão as principais diferenças:

- 100% open source
- Não está acoplado a nenhum provedor. Embora recomendemos os modelos que oferecemos pelo [Forge Core](https://forge.ai/core); o Forge pode ser usado com Claude, OpenAI, Google ou até modelos locais. À medida que os modelos evoluem, as diferenças diminuem e os preços caem, então ser provider-agnostic é importante.
- Suporte a LSP pronto para uso
- Foco em TUI. O Forge é construído por usuários de neovim e pelos criadores do [terminal.shop](https://terminal.shop); vamos levar ao limite o que é possível no terminal.
- Arquitetura cliente/servidor. Isso, por exemplo, permite executar o Forge no seu computador enquanto você o controla remotamente por um aplicativo mobile. Isso significa que o frontend TUI é apenas um dos possíveis clientes.

---

**Junte-se à nossa comunidade** [Discord](https://discord.gg/forge) | [X.com](https://x.com/forge)
