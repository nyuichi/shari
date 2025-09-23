# Shari Language Support

VS Code extension providing basic syntax highlighting and bracket configuration for the Shari proof language.

## Features
- Syntax highlighting for core keywords, declarations, literals, and comments
- Comment toggles for single-line (`--`) and block (`/- ... -/`) comments
- Auto-closing and surrounding pairs for common delimiters, including `« »`

## Installation
1. Install the VS Code extension CLI if you don't already have it: `npm install -g @vscode/vsce`.
2. Package the extension from this directory: `vsce package`. This produces a `.vsix` archive such as `shari-syntax-0.0.1.vsix`.
3. Install the packaged archive into VS Code: `code --install-extension shari-syntax-0.0.1.vsix`.
4. Reload VS Code; the Shari language support appears as an installed extension.

## Development
This extension is intentionally light-weight and implemented via a TextMate grammar. Update `syntaxes/shari.tmLanguage.json` to refine tokenization rules.

To test locally:
1. Open this directory in VS Code (`code editors/shari-vscode`).
2. Run `npm install` (only needed if you add build tooling).
3. Press `F5` to launch an Extension Development Host.

## License
MIT
