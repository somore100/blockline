
 
# Blockline

**A scalable visual programming environment** — built to make coding easier without limiting advanced users.

![Status](https://img.shields.io/badge/status-planned%20%2F%20in%20development-yellow)
![License](https://img.shields.io/badge/license-MIT-green)

Blockline is a visual code editor that solves one specific problem: **remembering exact syntax**. Unlike most block-based tools, which are built for education and hit a ceiling fast, Blockline is designed as a professional workflow — a way to visually build *real* code without losing the flexibility of traditional programming.

## Preview

<p align="center">
  <img src="Blockline_2026-08-24_18-43-52.png" width="70%" alt="Blockline editor preview" />
</p>

## The Idea

Most visual programming tools fall into one of these traps:

- Made for beginners and children
- Too limited for larger projects
- Hard to transition out of into real programming

Blockline takes a different approach: instead of replacing code, it works as a **visual layer on top of programming languages**. You build logic using templates, variables, and customizable blocks, and Blockline generates properly formatted code automatically.

## Features

**Visual Code Building**
- Build programs using blocks
- Generate real, readable source code
- Avoid syntax mistakes entirely
- Focus on logic, not formatting

**Multi-Language Support**
Planned support: Python, JavaScript, C/C++, and custom user-added languages. Users will be able to define their own language definitions and block systems.

**Code ↔ Block Conversion**
A two-way workflow — Blocks → Code, and Code → Blocks. Start visually and switch to manual editing anytime, or import existing code and convert it into blocks.

**Custom Blocks**
Advanced users can build custom templates, custom logic blocks, and custom language extensions.

## Who It's For

| User | Benefit |
|---|---|
| **Beginners** | Learn programming concepts without worrying about syntax |
| **Intermediate developers** | Speed up development, cut repetitive coding |
| **Advanced developers** | Build reusable templates and workflows |

## Current Status

🟡 Planned / in development — the concept and architecture are being designed.

## Roadmap

**Core System**
- [ ] Block editor
- [ ] Code generation system
- [ ] Language template system
- [ ] Project management

**Advanced Features**
- [ ] Code importing
- [ ] Code-to-block conversion
- [ ] Plugin system
- [ ] Custom language support

## 👀 Sneak Peek: V2

A redesign is in the works that moves Blockline from a single flat canvas to a **node-and-wire model**:

- **Nodes instead of one big canvas** — functions, entry points, and logic become individual nodes you open and edit on their own, then arrange visually on a file-level map.
- **Wires you can see *and* draw** — calls between nodes show up as connections automatically, and dragging a wire between two nodes writes the underlying call for you. The graph and the code always stay in sync — one is never out of date with the other.
- **Import your own code** — drop in an existing file and Blockline will recognize what it can (functions, familiar patterns) and turn it into nodes, while anything it doesn't recognize stays as readable, editable raw code instead of breaking.
- **Smart slots** — start typing in a block's input, and if what you type matches a recognizable pattern, it snaps into structured sub-blocks automatically. If not, it just stays as plain text — no dead ends.

This is still in the planning/build phase, not shipped yet — but it's the direction Blockline is heading: less "block editor bolted onto code," more "visual and written code as two views of the same thing."

## Future Vision

Blockline aims to become a bridge between visual programming and traditional development.

> Not a toy programming tool. Not a replacement for code. A different way to create software.

## Contributing

Blockline is early — architecture and design decisions are still open. If you're interested in visual programming, language tooling, or code generation, watch the repo or open an issue with ideas.

## License

[MIT](LICENSE)


<img width="1366" height="696" alt="Blockline 2026-08-24 18-43-52" src="https://github.com/user-attachments/assets/94a86123-9b0a-4232-a3a9-a947dd7ef94f" />
<img width="1920" height="1080" alt="Blockline" src="https://github.com/user-attachments/assets/b878a455-ffbd-4e1c-a40d-a6f50821a985" />
