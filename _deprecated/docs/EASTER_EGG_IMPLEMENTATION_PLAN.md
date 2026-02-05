# Easter Egg Games Implementation Plan
## Tetris, Pong, and Doom Integration

**Status:** Ready to Implement  
**Priority:** Fun Feature (Low Priority, High Delight Factor)

---

## ✅ What I've Created

### 1. **KonamiCode.purs & .js** ✅
- Konami code detection utility
- Tracks key sequence
- Triggers callback on match
- Resets on mismatch

### 2. **GameManager.purs** ✅
- Main game manager component
- Game selection menu
- Game overlay system
- High score tracking (structure)

---

## 🚧 Next Steps: Game Implementations

### **Phase 1: Tetris (PureScript)**

**Reference:** Found 3 PureScript Tetris implementations:
- `foollbar/petris` - Simple implementation
- `emilhaugberg/purescript-tetris` - More complete
- `CarstenKoenig/TetrisPS` - Canvas-based

**Implementation:**
1. Create `Tetris.purs` component
2. Implement game logic (grid, pieces, rotation, line clearing)
3. Canvas rendering via FFI
4. Keyboard controls (arrow keys, space)
5. Score system and level progression

**Files to Create:**
```
src/sidepanel-ps/src/Sidepanel/Components/EasterEggs/Tetris/
├── Tetris.purs           # Main component
├── TetrisLogic.purs      # Game logic (grid, pieces, collision)
├── TetrisRenderer.purs   # Canvas rendering
├── TetrisTypes.purs      # Types (Piece, Grid, GameState)
└── TetrisFFI.js          # Canvas FFI bindings
```

---

### **Phase 2: Pong (PureScript)**

**Implementation:**
1. Create `Pong.purs` component
2. Simple physics (ball bouncing, paddle collision)
3. Canvas rendering
4. AI opponent (simple follow-ball AI)
5. Two-player mode (optional)

**Files to Create:**
```
src/sidepanel-ps/src/Sidepanel/Components/EasterEggs/Pong/
├── Pong.purs             # Main component
├── PongLogic.purs        # Game logic (physics, collision)
├── PongRenderer.purs     # Canvas rendering
├── PongAI.purs           # AI opponent
└── PongTypes.purs        # Types
```

---

### **Phase 3: Doom (js-dos FFI)**

**Package:** `js-dos` v8.3.20 (npm)

**Implementation:**
1. Install `js-dos` package
2. Create `Doom.purs` FFI wrapper
3. Create `DoomFFI.js` integration
4. Load Doom WAD file
5. Map keyboard/mouse controls
6. Handle save/load states

**Files to Create:**
```
src/sidepanel-ps/src/Sidepanel/Components/EasterEggs/Doom/
├── Doom.purs             # Main component wrapper
├── DoomFFI.purs          # FFI bindings
└── DoomFFI.js            # js-dos integration
```

**Doom WAD File:**
- Use shareware version (legal, free)
- Or user provides their own WAD
- Load from CDN or local file

---

## 🎮 Activation Methods

### **Already Implemented:**
- ✅ Konami code detection
- ✅ Game selection menu
- ✅ Game manager component

### **To Add:**
- [ ] Keyboard shortcuts in `KeyboardNavigation.purs`:
  - `Ctrl+Shift+T` → Tetris
  - `Ctrl+Shift+P` → Pong (when not command palette)
  - `Ctrl+Shift+D+D` → Doom (double D!)
- [ ] URL parameter detection (`?game=tetris`)
- [ ] Command palette secret commands (`IDDQD`, `tetris`, etc.)
- [ ] Logo click easter egg (10 rapid clicks)

---

## 🎨 Styling

### **Game Overlay CSS**
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

.game-selection-menu {
  background: var(--color-bg-elevated);
  border: 1px solid var(--color-border-default);
  border-radius: 8px;
  padding: 2rem;
  max-width: 600px;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.3);
}

.game-card {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  padding: 1.5rem;
  cursor: pointer;
  transition: transform 0.2s, box-shadow 0.2s;
}

.game-card:hover {
  transform: translateY(-4px);
  box-shadow: 0 4px 16px rgba(0, 0, 0, 0.2);
}
```

---

## 🔧 Integration into App.purs

### **Add to Slots:**
```purescript
type Slots = (
  ...
  , gameManager :: H.Slot GameManager.Query GameManager.Output Unit
)

_gameManager = H.Slot :: H.Slot GameManager.Query GameManager.Output Unit
```

### **Add to Render:**
```purescript
render state = HH.div_ [
  ...
  , HH.slot _gameManager unit GameManager.component unit HandleGameManagerOutput
]
```

### **Add Handler:**
```purescript
HandleGameManagerOutput output -> case output of
  GameManager.GameStarted game -> 
    -- Log game start, update analytics
    pure unit
  GameManager.GameEnded game score ->
    -- Save high score, show celebration
    pure unit
```

### **Add Keyboard Shortcuts:**
```purescript
-- In KeyboardNavigation.purs parseKeyboardAction:
| ctrlKey event && shiftKey event && key event == "t" = 
    Just OpenGameSelection
| ctrlKey event && shiftKey event && key event == "p" && not commandPaletteOpen = 
    Just OpenPong
```

---

## 📦 Dependencies

### **PureScript:**
- Canvas rendering (via FFI)
- Array operations (already have)
- Maybe/Either (already have)

### **JavaScript/npm:**
- `js-dos` - For Doom emulation
- Canvas API - Built-in browser API

### **Assets:**
- Doom WAD file (shareware version)
- Optional: Sound effects for Tetris/Pong

---

## 🎯 Features to Implement

### **Tetris:**
- [ ] 10x20 game grid
- [ ] 7 classic tetrominoes
- [ ] Piece rotation
- [ ] Line clearing with animation
- [ ] Score system (lines cleared)
- [ ] Level progression (speed increases)
- [ ] Next piece preview
- [ ] Ghost piece (where piece will land)
- [ ] Hold piece feature
- [ ] Game over detection
- [ ] High score persistence

### **Pong:**
- [ ] Ball physics (bouncing)
- [ ] Paddle movement
- [ ] Collision detection
- [ ] Score tracking (first to 11)
- [ ] AI opponent
- [ ] Two-player mode
- [ ] Ball speed increase
- [ ] Sound effects (optional)
- [ ] High score persistence

### **Doom:**
- [ ] js-dos integration
- [ ] WAD file loading
- [ ] Keyboard controls (WASD, arrows)
- [ ] Mouse look
- [ ] Save/load states
- [ ] Full-screen toggle
- [ ] Performance optimization
- [ ] Cheat codes support (IDDQD, IDKFA, etc.)

---

## 🎁 Bonus Features

### **Achievements:**
- **Tetris Master** - Clear 100 lines
- **Pong Champion** - Win 10 games
- **Doom Slayer** - Complete Episode 1
- **Easter Egg Hunter** - Find all games

### **High Score Leaderboard:**
- LocalStorage persistence
- Per-game leaderboards
- Personal best tracking
- Share scores (optional)

### **Easter Egg Chains:**
- Find Tetris → unlocks Pong hint
- Find Pong → unlocks Doom hint
- Find all three → unlock secret theme

---

## 🚀 Quick Start Implementation

### **Step 1: Wire Up GameManager**
1. Add `GameManager` to `App.purs` slots
2. Add render slot
3. Add output handler
4. Test Konami code detection

### **Step 2: Implement Tetris**
1. Start with game logic (grid, pieces)
2. Add canvas rendering
3. Add controls
4. Add scoring
5. Polish animations

### **Step 3: Implement Pong**
1. Simple physics
2. Canvas rendering
3. AI opponent
4. Scoring

### **Step 4: Integrate Doom**
1. Install js-dos
2. Create FFI wrapper
3. Load WAD file
4. Map controls
5. Test and optimize

---

## 📝 Notes

### **Performance:**
- Games run in overlay (don't affect main app)
- Use `requestAnimationFrame` for game loops
- Optimize canvas rendering
- Lazy load game assets

### **Legal:**
- Tetris: Original implementation (no copyright issues)
- Pong: Original implementation (no copyright issues)
- Doom: Use shareware version (legal) or user's own WAD

### **Discoverability:**
- Games are hidden but discoverable
- Konami code is well-known
- Keyboard shortcuts documented in help
- URL parameters for direct access

---

## ✅ Success Criteria

- [ ] Konami code unlocks game menu
- [ ] All three games playable
- [ ] Games run at 60 FPS
- [ ] Games respect theme
- [ ] High scores persist
- [ ] Smooth transitions
- [ ] No performance impact on main app
- [ ] Fun and polished experience

---

*"The best easter eggs are the ones that make you smile."* 🎮
