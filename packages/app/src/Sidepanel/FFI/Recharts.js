// Recharts FFI implementation
"use strict";

// For now, use a simple canvas-based chart implementation
// In production, this would use Recharts via React or direct DOM manipulation

exports.createLineChart = function(elementId) {
  return function(config) {
    return function(data) {
      return function() {
        var element = document.getElementById(elementId);
        if (!element) {
          console.error("Chart element not found:", elementId);
          return null;
        }
        
        // Create canvas for chart
        var canvas = document.createElement("canvas");
        canvas.width = config.width || 800;
        canvas.height = config.height || 400;
        canvas.style.width = "100%";
        canvas.style.height = "100%";
        element.appendChild(canvas);
        
        var ctx = canvas.getContext("2d");
        
        // Store chart state
        var chartState = {
          element: element,
          canvas: canvas,
          ctx: ctx,
          config: config,
          data: data,
          elementId: elementId
        };
        
        // Render initial chart
        renderChart(chartState);
        
        return chartState;
      };
    };
  };
};

exports.updateChartData = function(chart) {
  return function(data) {
    return function() {
      if (chart) {
        chart.data = data;
        renderChart(chart);
      }
    };
  };
};

exports.updateChartConfig = function(chart) {
  return function(config) {
    return function() {
      if (chart) {
        chart.config = config;
        renderChart(chart);
      }
    };
  };
};

exports.disposeChart = function(chart) {
  return function() {
    if (chart && chart.element && chart.canvas) {
      chart.element.removeChild(chart.canvas);
    }
  };
};

// Simple line chart rendering
function renderChart(chart) {
  if (!chart || !chart.data || chart.data.length === 0) {
    return;
  }
  
  var ctx = chart.ctx;
  var canvas = chart.canvas;
  var data = chart.data;
  var config = chart.config;
  
  var width = canvas.width;
  var height = canvas.height;
  var padding = 40;
  var chartWidth = width - (padding * 2);
  var chartHeight = height - (padding * 2);
  
  // Clear canvas
  ctx.clearRect(0, 0, width, height);
  
  // Draw background
  ctx.fillStyle = "#ffffff";
  ctx.fillRect(0, 0, width, height);
  
  // Find max values for scaling
  var maxTokens = 0;
  var maxCost = 0;
  for (var i = 0; i < data.length; i++) {
    if (data[i].totalTokens > maxTokens) {
      maxTokens = data[i].totalTokens;
    }
    if (data[i].cost > maxCost) {
      maxCost = data[i].cost;
    }
  }
  
  // Draw axes
  ctx.strokeStyle = "#cccccc";
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.moveTo(padding, padding);
  ctx.lineTo(padding, height - padding);
  ctx.lineTo(width - padding, height - padding);
  ctx.stroke();
  
  // Draw grid lines
  ctx.strokeStyle = "#f0f0f0";
  for (var i = 0; i <= 5; i++) {
    var y = padding + (chartHeight * i / 5);
    ctx.beginPath();
    ctx.moveTo(padding, y);
    ctx.lineTo(width - padding, y);
    ctx.stroke();
  }
  
  // Draw data lines
  if (data.length > 1) {
    var stepX = chartWidth / (data.length - 1);
    
    // Draw total tokens line
    ctx.strokeStyle = "#4a90e2";
    ctx.lineWidth = 2;
    ctx.beginPath();
    for (var i = 0; i < data.length; i++) {
      var x = padding + (i * stepX);
      var y = height - padding - ((data[i].totalTokens / maxTokens) * chartHeight);
      if (i === 0) {
        ctx.moveTo(x, y);
      } else {
        ctx.lineTo(x, y);
      }
    }
    ctx.stroke();
    
    // Draw breakdown if enabled
    if (config.showBreakdown) {
      // Prompt tokens
      ctx.strokeStyle = "#7ed321";
      ctx.lineWidth = 2;
      ctx.beginPath();
      for (var i = 0; i < data.length; i++) {
        var x = padding + (i * stepX);
        var y = height - padding - ((data[i].promptTokens / maxTokens) * chartHeight);
        if (i === 0) {
          ctx.moveTo(x, y);
        } else {
          ctx.lineTo(x, y);
        }
      }
      ctx.stroke();
      
      // Completion tokens
      ctx.strokeStyle = "#f5a623";
      ctx.lineWidth = 2;
      ctx.beginPath();
      for (var i = 0; i < data.length; i++) {
        var x = padding + (i * stepX);
        var y = height - padding - ((data[i].completionTokens / maxTokens) * chartHeight);
        if (i === 0) {
          ctx.moveTo(x, y);
        } else {
          ctx.lineTo(x, y);
        }
      }
      ctx.stroke();
    }
    
    // Draw cost line if enabled
    if (config.showCost && maxCost > 0) {
      ctx.strokeStyle = "#bd10e0";
      ctx.lineWidth = 2;
      ctx.setLineDash([5, 5]);
      ctx.beginPath();
      for (var i = 0; i < data.length; i++) {
        var x = padding + (i * stepX);
        var y = height - padding - ((data[i].cost / maxCost) * chartHeight);
        if (i === 0) {
          ctx.moveTo(x, y);
        } else {
          ctx.lineTo(x, y);
        }
      }
      ctx.stroke();
      ctx.setLineDash([]);
    }
  }
  
  // Draw labels
  ctx.fillStyle = "#666666";
  ctx.font = "12px sans-serif";
  ctx.textAlign = "center";
  ctx.fillText("Time", width / 2, height - 10);
  
  ctx.save();
  ctx.translate(15, height / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.textAlign = "center";
  ctx.fillText("Tokens", 0, 0);
  ctx.restore();
  
  // Draw legend
  var legendY = 20;
  ctx.font = "11px sans-serif";
  ctx.textAlign = "left";
  
  ctx.fillStyle = "#4a90e2";
  ctx.fillRect(width - 150, legendY, 10, 10);
  ctx.fillStyle = "#333333";
  ctx.fillText("Total", width - 135, legendY + 8);
  
  if (config.showBreakdown) {
    ctx.fillStyle = "#7ed321";
    ctx.fillRect(width - 150, legendY + 15, 10, 10);
    ctx.fillStyle = "#333333";
    ctx.fillText("Prompt", width - 135, legendY + 23);
    
    ctx.fillStyle = "#f5a623";
    ctx.fillRect(width - 150, legendY + 30, 10, 10);
    ctx.fillStyle = "#333333";
    ctx.fillText("Completion", width - 135, legendY + 38);
  }
  
  if (config.showCost) {
    ctx.strokeStyle = "#bd10e0";
    ctx.lineWidth = 2;
    ctx.setLineDash([5, 5]);
    ctx.beginPath();
    ctx.moveTo(width - 150, legendY + 45);
    ctx.lineTo(width - 140, legendY + 45);
    ctx.stroke();
    ctx.setLineDash([]);
    ctx.fillStyle = "#333333";
    ctx.fillText("Cost", width - 135, legendY + 48);
  }
}

// Pie chart functions
exports.createPieChart = function(elementId) {
  return function(config) {
    return function(data) {
      return function() {
        var element = document.getElementById(elementId);
        if (!element) {
          console.error("Chart element not found:", elementId);
          return null;
        }
        
        // Create canvas for chart
        var canvas = document.createElement("canvas");
        canvas.width = config.width || 400;
        canvas.height = config.height || 400;
        canvas.style.width = "100%";
        canvas.style.height = "100%";
        element.appendChild(canvas);
        
        var ctx = canvas.getContext("2d");
        
        // Store chart state
        var chartState = {
          element: element,
          canvas: canvas,
          ctx: ctx,
          config: config,
          data: data,
          elementId: elementId
        };
        
        // Render initial chart
        renderPieChart(chartState);
        
        return chartState;
      };
    };
  };
};

exports.updatePieChartData = function(chart) {
  return function(data) {
    return function() {
      if (chart) {
        chart.data = data;
        renderPieChart(chart);
      }
    };
  };
};

// Simple pie chart rendering
function renderPieChart(chart) {
  if (!chart || !chart.data || chart.data.length === 0) {
    return;
  }
  
  var ctx = chart.ctx;
  var canvas = chart.canvas;
  var data = chart.data;
  var config = chart.config;
  
  var width = canvas.width;
  var height = canvas.height;
  var centerX = width / 2;
  var centerY = height / 2;
  var radius = Math.min(width, height) / 2 - 20;
  
  // Clear canvas
  ctx.clearRect(0, 0, width, height);
  
  // Draw background
  ctx.fillStyle = "#ffffff";
  ctx.fillRect(0, 0, width, height);
  
  // Calculate total for percentage
  var total = 0;
  for (var i = 0; i < data.length; i++) {
    total += data[i].value;
  }
  
  // Draw pie slices
  var startAngle = -Math.PI / 2; // Start at top
  for (var i = 0; i < data.length; i++) {
    var sliceAngle = (data[i].value / total) * 2 * Math.PI;
    
    // Draw slice
    ctx.beginPath();
    ctx.moveTo(centerX, centerY);
    ctx.arc(centerX, centerY, radius, startAngle, startAngle + sliceAngle);
    ctx.closePath();
    ctx.fillStyle = data[i].color || "#cccccc";
    ctx.fill();
    ctx.strokeStyle = "#ffffff";
    ctx.lineWidth = 2;
    ctx.stroke();
    
    // Draw label if enabled
    if (config.showLabels) {
      var labelAngle = startAngle + sliceAngle / 2;
      var labelX = centerX + Math.cos(labelAngle) * (radius * 0.7);
      var labelY = centerY + Math.sin(labelAngle) * (radius * 0.7);
      
      ctx.fillStyle = "#333333";
      ctx.font = "12px sans-serif";
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText(data[i].label, labelX, labelY);
      
      if (config.showPercentages) {
        ctx.font = "10px sans-serif";
        ctx.fillText(data[i].percentage.toFixed(1) + "%", labelX, labelY + 15);
      }
    }
    
    startAngle += sliceAngle;
  }
}
