// | FFI JavaScript bindings for agent social
// | All operations are deterministic - accept explicit parameters

const { createHash } = require('crypto');

// | Generate deterministic ID from namespace and seed
// | Uses SHA-256 hash for deterministic UUID-like ID
exports.generateIdFromSeed = function(namespace) {
  return function(seed) {
    const input = namespace + ':' + seed.toString();
    const hash = createHash('sha256').update(input).digest('hex');
    const uuid = hash.substring(0, 32);
    return uuid.substring(0, 8) + '-' +
           uuid.substring(8, 12) + '-' +
           uuid.substring(12, 16) + '-' +
           uuid.substring(16, 20) + '-' +
           uuid.substring(20, 32);
  };
};

// | Format timestamp (milliseconds since epoch) as ISO 8601 string
// | Deterministic: same input always produces same output
exports.formatTimestamp = function(timestampMs) {
  return new Date(timestampMs).toISOString();
};

// | Generate deterministic avatar URL from agent ID
// | Uses SHA-256 hash to select avatar color and generate initials
// | Returns data URL for SVG avatar (deterministic)
exports.generateAvatarUrl = function(agentId) {
  return function(displayName) {
    const hash = createHash('sha256').update(agentId).digest('hex');
    
    // Select color from hash (6 colors available)
    const colorIndex = parseInt(hash.substring(0, 2), 16) % 6;
    const colors = [
      { bg: '#FF6B9D', fg: '#FFFFFF' }, // pink
      { bg: '#00D9A5', fg: '#FFFFFF' }, // mint
      { bg: '#FF8C42', fg: '#FFFFFF' }, // orange
      { bg: '#9B59B6', fg: '#FFFFFF' }, // purple
      { bg: '#00CED1', fg: '#FFFFFF' }, // cyan
      { bg: '#32CD32', fg: '#FFFFFF' }  // lime
    ];
    const color = colors[colorIndex];
    
    // Generate initials from display name
    const initials = displayName
      .split(' ')
      .map(word => word.charAt(0).toUpperCase())
      .slice(0, 2)
      .join('');
    
    // Create SVG avatar
    const svg = `<svg width="64" height="64" xmlns="http://www.w3.org/2000/svg">
      <rect width="64" height="64" fill="${color.bg}" rx="32"/>
      <text x="32" y="32" font-family="Arial, sans-serif" font-size="24" font-weight="bold" 
            fill="${color.fg}" text-anchor="middle" dominant-baseline="central">${initials}</text>
    </svg>`;
    
    // Return as data URL
    return 'data:image/svg+xml;base64,' + Buffer.from(svg).toString('base64');
  };
};

// | Generate avatar URL from semantic cell state
// | Uses cell position (first 3 dims) for color, energy for brightness, grade for opacity, spin for rotation
// | Returns data URL for SVG avatar (deterministic based on cell state)
exports.generateAvatarFromCellState = function(agentId) {
  return function(displayName) {
    return function(cellStateJson) {
      try {
        // Parse cell state JSON
        // Expected format: { position: [512 floats], energy: 0-1, grade: 0-1, spin: [x, y, z] }
        const cellState = JSON.parse(cellStateJson);
        
        // Extract cell state properties
        const position = cellState.position || [];
        const energy = Math.max(0, Math.min(1, cellState.energy || 0.5));
        const grade = Math.max(0, Math.min(1, cellState.grade || 0.5));
        const spin = cellState.spin || [0, 0, 0];
        
        // Map position (first 3 dims) to HSL color space
        // Normalize position values to [0, 1] range (assuming they're in [-1, 1] or similar)
        const pos0 = ((position[0] || 0) + 1) / 2; // Normalize to [0, 1]
        const pos1 = ((position[1] || 0) + 1) / 2;
        const pos2 = ((position[2] || 0) + 1) / 2;
        
        // Convert to HSL: H from pos0, S from pos1, L from energy
        const hue = Math.floor(pos0 * 360); // 0-360 degrees
        const saturation = Math.floor(pos1 * 100); // 0-100%
        const lightness = Math.floor(30 + energy * 40); // 30-70% (energy affects brightness)
        
        // Convert HSL to RGB
        const hslToRgb = (h, s, l) => {
          s /= 100;
          l /= 100;
          const c = (1 - Math.abs(2 * l - 1)) * s;
          const x = c * (1 - Math.abs((h / 60) % 2 - 1));
          const m = l - c / 2;
          let r, g, b;
          if (h < 60) { r = c; g = x; b = 0; }
          else if (h < 120) { r = x; g = c; b = 0; }
          else if (h < 180) { r = 0; g = c; b = x; }
          else if (h < 240) { r = 0; g = x; b = c; }
          else if (h < 300) { r = x; g = 0; b = c; }
          else { r = c; g = 0; b = x; }
          return [
            Math.round((r + m) * 255),
            Math.round((g + m) * 255),
            Math.round((b + m) * 255)
          ];
        };
        
        const [r, g, b] = hslToRgb(hue, saturation, lightness);
        const bgColor = `rgb(${r}, ${g}, ${b})`;
        
        // Text color: white if background is dark, black if light
        const textColor = lightness < 50 ? '#FFFFFF' : '#000000';
        
        // Opacity based on grade (confidence)
        const opacity = 0.7 + grade * 0.3; // 0.7-1.0
        
        // Rotation based on spin (attention direction)
        // Use spin[0] and spin[1] to determine rotation angle
        const rotationAngle = Math.atan2(spin[1] || 0, spin[0] || 0) * 180 / Math.PI;
        
        // Generate initials from display name
        const initials = displayName
          .split(' ')
          .map(word => word.charAt(0).toUpperCase())
          .slice(0, 2)
          .join('');
        
        // Create SVG avatar with cell state visualization
        const svg = `<svg width="64" height="64" xmlns="http://www.w3.org/2000/svg">
      <defs>
        <pattern id="gradePattern" x="0" y="0" width="8" height="8" patternUnits="userSpaceOnUse">
          <circle cx="4" cy="4" r="${grade * 2}" fill="${textColor}" opacity="0.2"/>
        </pattern>
      </defs>
      <rect width="64" height="64" fill="${bgColor}" rx="32" opacity="${opacity}"/>
      <rect width="64" height="64" fill="url(#gradePattern)" rx="32"/>
      <g transform="rotate(${rotationAngle} 32 32)">
        <text x="32" y="32" font-family="Arial, sans-serif" font-size="24" font-weight="bold" 
              fill="${textColor}" text-anchor="middle" dominant-baseline="central">${initials}</text>
      </g>
    </svg>`;
        
        // Return as data URL
        return 'data:image/svg+xml;base64,' + Buffer.from(svg).toString('base64');
      } catch (e) {
        // Fallback to default avatar generation if cell state parsing fails
        return exports.generateAvatarUrl(agentId)(displayName);
      }
    };
  };
};
