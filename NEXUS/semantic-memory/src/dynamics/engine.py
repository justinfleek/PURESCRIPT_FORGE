"""
Nexus Semantic Memory - Dynamics Engine
Prediction loop with 10ms tick for semantic cell evolution
"""

import time
from typing import List, Dict
from threading import Thread, Event
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent / "semantic-cells" / "src"))
from core.types import SemanticCell, CellState


class DynamicsEngine:
    """
    Dynamics engine for semantic cell evolution.
    
    Runs prediction loop at 10ms intervals to update cell states:
    - Position (concept location in semantic space)
    - Velocity (concept movement)
    - Acceleration (concept change rate)
    - Spin (concept rotation)
    - Grade (concept quality)
    - Energy (concept uncertainty/exploration value)
    """
    
    def __init__(self, cells: List[SemanticCell], tick_interval_ms: float = 10.0):
        """
        Initialize dynamics engine.
        
        Args:
            cells: List of semantic cells
            tick_interval_ms: Tick interval in milliseconds
        """
        self.cells = {cell.id: cell for cell in cells}
        self.tick_interval_ms = tick_interval_ms
        self.running = False
        self.thread = None
        self.stop_event = Event()
    
    def start(self) -> None:
        """Start dynamics engine"""
        if self.running:
            return
        
        self.running = True
        self.stop_event.clear()
        self.thread = Thread(target=self._run_loop, daemon=True)
        self.thread.start()
    
    def stop(self) -> None:
        """Stop dynamics engine"""
        if not self.running:
            return
        
        self.running = False
        self.stop_event.set()
        if self.thread:
            self.thread.join(timeout=1.0)
    
    def _run_loop(self) -> None:
        """Run prediction loop"""
        tick_interval_sec = self.tick_interval_ms / 1000.0
        
        while self.running and not self.stop_event.is_set():
            start_time = time.time()
            
            # Update all cells
            self._tick()
            
            # Sleep to maintain tick interval
            elapsed = time.time() - start_time
            sleep_time = max(0, tick_interval_sec - elapsed)
            time.sleep(sleep_time)
    
    def _tick(self) -> None:
        """Single tick of dynamics engine"""
        for cell_id, cell in self.cells.items():
            self._update_cell_state(cell)
    
    def _update_cell_state(self, cell: SemanticCell) -> None:
        """
        Update cell state based on dynamics.
        
        Args:
            cell: Semantic cell to update
        """
        state = cell.state
        
        # Update acceleration (based on couplings and energy)
        # Higher energy -> more exploration -> more acceleration
        energy_factor = state.energy
        
        # Random walk with energy-dependent magnitude
        import random
        acceleration_noise = [
            random.gauss(0, 0.01 * energy_factor) for _ in range(3)
        ]
        
        state.acceleration = [
            state.acceleration[i] + acceleration_noise[i]
            for i in range(3)
        ]
        
        # Update velocity (integrate acceleration)
        dt = self.tick_interval_ms / 1000.0
        state.velocity = [
            state.velocity[i] + state.acceleration[i] * dt
            for i in range(3)
        ]
        
        # Damping (velocity decays over time)
        damping = 0.99
        state.velocity = [v * damping for v in state.velocity]
        
        # Update position (integrate velocity)
        state.position = [
            state.position[i] + state.velocity[i] * dt
            for i in range(3)
        ]
        
        # Update spin (rotational motion)
        spin_acceleration = random.gauss(0, 0.001 * energy_factor)
        state.spin += spin_acceleration * dt
        state.spin *= damping
        
        # Update energy (uncertainty/exploration value)
        # Energy increases when cell is explored (couplings added)
        # Energy decreases when cell is well-understood (many couplings)
        coupling_count = len(cell.coupling_ids)
        exploration_bonus = 0.001  # Small bonus per tick
        understanding_penalty = coupling_count * 0.0001  # Penalty for many couplings
        
        state.energy += exploration_bonus - understanding_penalty
        state.energy = max(0.0, min(1.0, state.energy))  # Clamp to [0, 1]
        
        # Update grade (quality measure)
        # Grade improves with exploration and coupling strength
        grade_improvement = 0.0001 * energy_factor
        state.grade += grade_improvement
        state.grade = max(0.0, min(1.0, state.grade))  # Clamp to [0, 1]
    
    def add_cell(self, cell: SemanticCell) -> None:
        """
        Add cell to dynamics engine.
        
        Args:
            cell: Semantic cell
        """
        self.cells[cell.id] = cell
    
    def remove_cell(self, cell_id: str) -> None:
        """
        Remove cell from dynamics engine.
        
        Args:
            cell_id: Cell ID
        """
        if cell_id in self.cells:
            del self.cells[cell_id]
    
    def get_cells(self) -> List[SemanticCell]:
        """
        Get all cells.
        
        Returns:
            List of semantic cells
        """
        return list(self.cells.values())
