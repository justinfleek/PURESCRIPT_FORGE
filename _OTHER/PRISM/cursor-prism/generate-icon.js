const { createCanvas } = require('canvas');
const fs = require('fs');

const size = 128;
const canvas = createCanvas(size, size);
const ctx = canvas.getContext('2d');

// Background circle (dark)
ctx.beginPath();
ctx.arc(size/2, size/2, size/2 - 4, 0, Math.PI * 2);
const bgGrad = ctx.createRadialGradient(size/2, size/2, 0, size/2, size/2, size*0.7);
bgGrad.addColorStop(0, '#1a1a1a');
bgGrad.addColorStop(1, '#0a0a0a');
ctx.fillStyle = bgGrad;
ctx.fill();
ctx.strokeStyle = '#2a2a2a';
ctx.lineWidth = 2;
ctx.stroke();

// Prism gradient
const prismGrad = ctx.createLinearGradient(28, 20, 100, 90);
prismGrad.addColorStop(0, '#00a0e4');
prismGrad.addColorStop(0.33, '#3cb878');
prismGrad.addColorStop(0.66, '#ffd93d');
prismGrad.addColorStop(1, '#ff6b35');

// Glow effect
ctx.shadowColor = '#3cb878';
ctx.shadowBlur = 10;

// Prism triangle
ctx.beginPath();
ctx.moveTo(64, 22);
ctx.lineTo(98, 88);
ctx.lineTo(30, 88);
ctx.closePath();
ctx.strokeStyle = prismGrad;
ctx.lineWidth = 4;
ctx.lineJoin = 'round';
ctx.stroke();

ctx.shadowBlur = 0;

// Incoming light beam (white)
ctx.beginPath();
ctx.moveTo(18, 48);
ctx.lineTo(50, 54);
ctx.strokeStyle = 'rgba(255, 255, 255, 0.9)';
ctx.lineWidth = 3;
ctx.lineCap = 'round';
ctx.stroke();

// Dispersed beams
const beams = [
  { x1: 78, y1: 54, x2: 108, y2: 34, color: '#00a0e4' },
  { x1: 80, y1: 59, x2: 110, y2: 49, color: '#3cb878' },
  { x1: 82, y1: 64, x2: 112, y2: 64, color: '#ffd93d' },
  { x1: 80, y1: 69, x2: 110, y2: 79, color: '#ff6b35' },
];

ctx.lineWidth = 2.5;
beams.forEach(beam => {
  ctx.beginPath();
  ctx.moveTo(beam.x1, beam.y1);
  ctx.lineTo(beam.x2, beam.y2);
  ctx.strokeStyle = beam.color;
  ctx.stroke();
});

// Highlight dots
ctx.beginPath();
ctx.arc(64, 22, 3, 0, Math.PI * 2);
ctx.fillStyle = 'rgba(255, 255, 255, 0.8)';
ctx.fill();

// Save
const buffer = canvas.toBuffer('image/png');
fs.writeFileSync('media/icon.png', buffer);
console.log('✓ Created media/icon.png (128x128)');
