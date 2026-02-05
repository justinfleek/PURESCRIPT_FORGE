# Easter Egg Games: Hidden Mini-Games in the Sidepanel
## Tetris, Pong, and Doom Integration

**Status:** Proposal & Implementation Plan  
**Date:** 2026-02-04

---

## 🎮 Game Selection

### 1. **Tetris** 🧩
- **Classic puzzle game** - Perfect for quick breaks
- **Small footprint** - Can be implemented in PureScript or via FFI
- **Keyboard controls** - Arrow keys for movement, space for drop
- **Hidden trigger** - Konami code or secret shortcut

### 2. **Pong** 🏓
- **Classic arcade game** - Simple, nostalgic
- **Two-player or AI** - Play against AI or friend
- **Minimal UI** - Fits sidepanel aesthetic
- **Hidden trigger** - Secret keyboard combo

### 3. **Doom** 🔫
- **Classic FPS** - The ultimate easter egg
- **js-dos port** - Browser-based DOS emulator
- **Full game** - Complete Doom experience
- **Hidden trigger** - Most secret activation

---

## 🎯 Activation Methods

### **Konami Code** (Up Up Down Down Left Right Left Right B A)
- Universal easter egg trigger
- Works from anywhere in the app
- Shows game selection menu

### **Secret Keyboard Shortcuts**
- **Ctrl+Shift+T** - Tetris
- **Ctrl+Shift+P** - Pong  
- **Ctrl+Shift+D** - Doom (double D for Doom!)

### **Hidden UI Elements**
- Click logo 10 times rapidly
- Hold Shift+Alt and click version number
- Type "IDDQD" in command palette (Doom cheat code!)

### **URL Parameters**
- `?game=tetris`
- `?game=pong`
- `?game=doom`

---

## 🏗️ Implementation Architecture

### **Game Manager Component**
```purescript
module Sidepanel.Components.EasterEggs.GameManager where

-- Game types
data Game = Tetris | Pong | Doom

-- Game state
type GameState = 
  { activeGame :: Maybe Game
  , konamiSequence :: Array KeyCode
  , isUnlocked :: Boolean
  }
```

### **Integration Points**

1. **KeyboardNavigation.purs** - Detect Konami code
2. **CommandPalette.purs** - Secret commands
3. **App.purs** - Game overlay rendering
4. **New Game Components** - Individual game implementations

---

## 🎨 UI Design

### **Game Selection Menu**
```
┌─────────────────────────────────────────┐
│  🎮 EASTER EGG GAMES            [✕]   │
├─────────────────────────────────────────┤
│                                         │
│  ┌─────────────┐  ┌─────────────┐     │
│  │   🧩        │  │   🏓        │     │
│  │  TETRIS     │  │   PONG      │     │
│  │             │  │             │     │
│  │  [Play]     │  │  [Play]     │     │
│  └─────────────┘  └─────────────┘     │
│                                         │
│  ┌─────────────┐                       │
│  │   🔫        │                       │
│  │   DOOM      │                       │
│  │             │                       │
│  │  [Play]     │                       │
│  └─────────────┘                       │
│                                         │
│  Press ESC to exit                     │
└─────────────────────────────────────────┘
```

### **In-Game Overlay**
- **Full-screen overlay** - Covers entire sidepanel
- **Exit button** - Top-right corner
- **Score display** - Top-left corner
- **Pause menu** - ESC key
- **Theme-aware** - Matches current theme

---

## 🧩 Tetris Implementation

### **PureScript Implementation**
- **Grid-based** - 10x20 game board
- **Piece rotation** - 7 classic tetrominoes
- **Line clearing** - Animated line removal
- **Score system** - Points for lines cleared
- **Level progression** - Speed increases

### **Controls**
- **Arrow Left/Right** - Move piece
- **Arrow Down** - Soft drop
- **Arrow Up** - Rotate
- **Space** - Hard drop
- **P** - Pause
- **ESC** - Exit

### **Features**
- **Ghost piece** - Show where piece will land
- **Next piece preview** - Show upcoming piece
- **Hold piece** - Save piece for later
- **Particle effects** - When lines clear

---

## 🏓 Pong Implementation

### **PureScript Implementation**
- **Canvas-based** - HTML5 canvas rendering
- **Physics** - Ball collision and bouncing
- **AI opponent** - Simple AI paddle
- **Two-player** - Local multiplayer option

### **Controls**
- **W/S** - Player 1 paddle (left)
- **Arrow Up/Down** - Player 2 paddle (right)
- **Space** - Serve ball
- **P** - Pause
- **ESC** - Exit

### **Features**
- **Score tracking** - First to 11 wins
- **Ball speed increase** - Gets faster over time
- **Power-ups** (optional) - Bigger paddle, faster ball
- **Retro sound effects** - Classic beep sounds

---

## 🔫 Doom Implementation

### **js-dos Integration**
- **DOS emulator** - Run original Doom in browser
- **FFI wrapper** - PureScript interface to js-dos
- **Full game** - Complete Doom experience
- **Save states** - Save/load game progress

### **Setup**
```javascript
// js-dos integration
import { DosBox } from "js-dos";

const dosbox = new DosBox({
  canvas: document.getElementById("doom-canvas"),
  onready: () => {
    dosbox.run("doom.wad");
  }
});
```

### **Controls**
- **WASD** - Move
- **Mouse** - Look around
- **Space** - Shoot
- **E** - Use/Open
- **ESC** - Menu
- **Tab** - Map

### **Features**
- **Full Doom game** - All levels, weapons, enemies
- **Save/Load** - Persist game state
- **Cheat codes** - Classic Doom cheats work!
- **Performance** - Optimized for sidepanel

---

## 🎯 Implementation Plan

### **Phase 1: Infrastructure (Week 1)**
1. ✅ Create `GameManager` component
2. ✅ Add Konami code detection to `KeyboardNavigation`
3. ✅ Add secret commands to `CommandPalette`
4. ✅ Create game overlay system
5. ✅ Add game state to `AppState`

### **Phase 2: Tetris (Week 2)**
1. ✅ Implement Tetris game logic in PureScript
2. ✅ Create Tetris component with canvas rendering
3. ✅ Add controls and scoring
4. ✅ Polish animations and effects
5. ✅ Test and optimize

### **Phase 3: Pong (Week 3)**
1. ✅ Implement Pong game logic
2. ✅ Create Pong component
3. ✅ Add AI opponent
4. ✅ Add two-player mode
5. ✅ Polish and test

### **Phase 4: Doom (Week 4)**
1. ✅ Integrate js-dos via FFI
2. ✅ Create Doom wrapper component
3. ✅ Add Doom WAD file loading
4. ✅ Implement controls mapping
5. ✅ Add save/load functionality
6. ✅ Optimize performance

### **Phase 5: Polish (Week 5)**
1. ✅ Add game selection menu
2. ✅ Add high score tracking
3. ✅ Add achievements/badges
4. ✅ Add sound effects
5. ✅ Add particle effects
6. ✅ Final testing

---

## 📁 File Structure

```
src/sidepanel-ps/src/Sidepanel/
├── Components/
│   └── EasterEggs/
│       ├── GameManager.purs          # Main game manager
│       ├── GameSelection.purs        # Game selection menu
│       ├── Tetris/
│       │   ├── Tetris.purs           # Tetris game component
│       │   ├── TetrisLogic.purs      # Game logic
│       │   ├── TetrisRenderer.purs   # Canvas rendering
│       │   └── TetrisTypes.purs      # Types
│       ├── Pong/
│       │   ├── Pong.purs             # Pong game component
│       │   ├── PongLogic.purs        # Game logic
│       │   ├── PongRenderer.purs     # Canvas rendering
│       │   └── PongAI.purs           # AI opponent
│       └── Doom/
│           ├── Doom.purs             # Doom wrapper component
│           ├── DoomFFI.purs          # js-dos FFI bindings
│           └── DoomFFI.js            # JavaScript integration
├── Utils/
│   └── KonamiCode.purs               # Konami code detection
└── State/
    └── Games.purs                    # Game state management
```

---

## 🎨 Styling

### **Game Overlay Styles**
```css
.game-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: var(--color-bg-base);
  z-index: 9999;
  display: flex;
  align-items: center;
  justify-content: center;
}

.game-container {
  width: 100%;
  height: 100%;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
}

.game-exit {
  position: absolute;
  top: 1rem;
  right: 1rem;
  z-index: 10000;
}
```

### **Theme Integration**
- Games respect current theme
- Dark mode optimized
- Smooth transitions
- Consistent with sidepanel design

---

## 🎯 Features

### **High Score Tracking**
- LocalStorage persistence
- Per-game leaderboards
- Personal best tracking
- Achievement unlocks

### **Achievements**
- **Tetris Master** - Clear 100 lines
- **Pong Champion** - Win 10 games
- **Doom Slayer** - Complete Episode 1
- **Easter Egg Hunter** - Find all games

### **Sound Effects**
- Optional sound effects
- Can be muted
- Retro 8-bit sounds
- Theme-aware volume

### **Performance**
- 60 FPS target
- Optimized rendering
- Efficient game loops
- Memory management

---

## 🔧 Technical Details

### **Konami Code Detection**
```purescript
-- Sequence: Up Up Down Down Left Right Left Right B A
konamiSequence :: Array KeyCode
konamiSequence = 
  [ ArrowUp, ArrowUp, ArrowDown, ArrowDown
  , ArrowLeft, ArrowRight, ArrowLeft, ArrowRight
  , KeyB, KeyA
  ]
```

### **Game State Management**
```purescript
type GameState =
  { activeGame :: Maybe Game
  , scores :: Map Game Int
  , achievements :: Set Achievement
  , settings :: GameSettings
  }

type GameSettings =
  { soundEnabled :: Boolean
  , difficulty :: Difficulty
  , controls :: ControlScheme
  }
```

### **FFI for Doom**
```purescript
foreign import data DosBox :: Type

foreign import createDosBox :: String -> Effect DosBox
foreign import loadGame :: DosBox -> String -> Effect Unit
foreign import sendKey :: DosBox -> String -> Effect Unit
foreign import destroyDosBox :: DosBox -> Effect Unit
```

---

## 🎁 Bonus Features

### **Secret Unlocks**
- **Beat Tetris** - Unlock special theme
- **Perfect Pong** - Unlock achievement badge
- **Doom Completion** - Unlock secret mode

### **Easter Egg Chains**
- Find Tetris → unlocks Pong hint
- Find Pong → unlocks Doom hint
- Find all three → unlock secret menu

### **Social Features**
- Share high scores (optional)
- Compare with friends
- Weekly challenges

---

## 📝 Implementation Notes

### **PureScript vs JavaScript**
- **Tetris & Pong**: Pure PureScript implementation (better type safety)
- **Doom**: JavaScript via FFI (too complex for PureScript)

### **Performance Considerations**
- Use `requestAnimationFrame` for game loops
- Virtualize large game boards if needed
- Optimize canvas rendering
- Lazy load game assets

### **Accessibility**
- Keyboard-only controls
- Screen reader announcements
- High contrast mode support
- Configurable difficulty

---

## 🚀 Getting Started

### **Step 1: Create Game Manager**
```purescript
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \_ -> { activeGame: Nothing, ... }
  , render: renderGameManager
  , eval: H.mkEval $ H.defaultEval { ... }
  }
```

### **Step 2: Add Konami Code Detection**
- Integrate into `KeyboardNavigation.purs`
- Track key sequence
- Trigger game menu on match

### **Step 3: Implement Tetris**
- Start with game logic
- Add rendering
- Add controls
- Polish and test

### **Step 4: Implement Pong**
- Similar to Tetris
- Add AI opponent
- Add two-player mode

### **Step 5: Integrate Doom**
- Set up js-dos FFI
- Load Doom WAD
- Map controls
- Test and optimize

---

## 🎮 Game Assets

### **Tetris**
- No external assets needed
- Pure code implementation

### **Pong**
- Simple shapes, no assets
- Optional sound effects

### **Doom**
- Need Doom WAD file
- Can use shareware version (legal)
- Or user provides their own

---

## ✅ Success Criteria

- [ ] All three games accessible via Konami code
- [ ] Games run at 60 FPS
- [ ] Games respect theme
- [ ] High scores persist
- [ ] Smooth transitions
- [ ] No performance impact on main app
- [ ] Games are discoverable but hidden
- [ ] Fun and polished experience

---

*"Sometimes the best features are the ones you have to discover."* 🎮
