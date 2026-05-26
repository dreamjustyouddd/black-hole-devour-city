/* =============================================================
   黑洞吞噬城市 - 核心游戏逻辑
   文件: game.js
   说明: 包含黑洞物理、物品系统、粒子效果、渲染引擎等全部逻辑
   ============================================================= */

// ===================== 全局常量 =====================
const GAME_DURATION   = 90;       // 游戏总时长（秒）
const WORLD_W         = 3000;     // 世界宽度
const WORLD_H         = 2000;     // 世界高度
const BASE_SPEED      = 5;        // 黑洞初始移动速度
const GRAVITY_FACTOR  = 3.5;      // 引力范围 = 半径 × 此系数
const ABSORB_RATIO    = 0.7;      // 物品需小于黑洞半径 × 此比例才能被吞噬
const GROWTH_RATE     = 0.15;     // 吞噬后黑洞增长系数
const SPEED_DECAY     = 0.985;    // 每次变大后速度衰减系数
const MIN_SPEED       = 1.5;      // 最低移动速度
const PULL_STRENGTH   = 0.12;     // 引力拉扯加速度
const STAR_THRESHOLD  = 80;       // 半径超过此值时出现星空背景
const SHAKE_THRESHOLD = 3;        // 物品大小超过此值触发屏幕震动
const HURRY_UP_TIME   = 30;       // 最后N秒倒计时加速
const HURRY_UP_FACTOR = 1.5;      // 加速期间每秒扣除的游戏秒数
const GEM_LIFETIME    = 5;        // 限时宝石存活时间（秒）
const GEM_SPAWN_INTERVAL = 15;    // 宝石生成间隔（秒）
const GEM_FIRST_DELAY = 10;       // 首颗宝石出现时间（秒）
const EDGE_MARGIN     = 350;      // 边缘建筑判定距离
const EDGE_REMOVAL_INTERVAL = 4;  // 边缘建筑消失间隔（秒）
const RAINBOW_SCORE       = 5000; // 分数达到此值时触发彩虹模式
const PENALTY_BUILDING_MAX  = 2;  // 每局最多生成的减分建筑数量
const PENALTY_BUILDING_SIZE = 105;// 减分建筑基础尺寸（约大厦1.5倍）
const PENALTY_SCORE         = 200;// 吞噬减分建筑扣除的分数
const PENALTY_RADIUS_SHRINK = 0.9;// 吞噬后黑洞半径缩放（缩小10%）
const PENALTY_SPEED_MULT    = 0.8;// 吞噬后速度缩放（降低20%）
const PENALTY_DEBUFF_TIME   = 3;  // 速度减益持续时间（秒）
const PENALTY_REPEL_RANGE   = 260;// 斥力场范围（像素）
const PENALTY_REPEL_FORCE   = 0.18;// 斥力场强度

/** 根据时间偏移返回 HSL 彩虹色字符串 */
function rainbowColor(timeOffset, alpha = 1) {
  const hue = ((Date.now() * 0.1 + timeOffset * 60) % 360 + 360) % 360;
  return alpha >= 1
    ? `hsl(${hue}, 100%, 60%)`
    : `hsla(${hue}, 100%, 60%, ${alpha})`;
}

// ===================== 城市路网定义 =====================
// 主干道（宽）
const MAIN_H_ROADS = [300, 800, 1300, 1800];   // 横向主干道 y 坐标
const MAIN_V_ROADS = [400, 1000, 1700, 2500];   // 纵向主干道 x 坐标
// 小马路（窄）
const SIDE_H_ROADS = [550, 1050, 1550];         // 横向小马路 y 坐标
const SIDE_V_ROADS = [700, 1350, 2100];         // 纵向小马路 x 坐标

const MAIN_ROAD_W = 36;   // 主干道宽度
const SIDE_ROAD_W = 20;   // 小马路宽度

/** 所有道路位置（用于快速查询） */
const ALL_H_ROADS = [...MAIN_H_ROADS, ...SIDE_H_ROADS].sort((a, b) => a - b);
const ALL_V_ROADS = [...MAIN_V_ROADS, ...SIDE_V_ROADS].sort((a, b) => a - b);

/** 路口检测容差 */
const INTERSECT_TOL = MAIN_ROAD_W * 0.6;

// ===================== DOM 引用 =====================
const canvas    = document.getElementById('gameCanvas');
const ctx       = canvas.getContext('2d');
const hudScore  = document.getElementById('score');
const hudRadius = document.getElementById('radius');
const hudTimer  = document.getElementById('timer');
const startScr  = document.getElementById('start-screen');
const endScr    = document.getElementById('end-screen');
const startBtn  = document.getElementById('startBtn');
const restartBtn= document.getElementById('restartBtn');

// ===================== 画布自适应 =====================
function resizeCanvas() {
  canvas.width  = window.innerWidth;
  canvas.height = window.innerHeight;
}
window.addEventListener('resize', resizeCanvas);
resizeCanvas();

// ===================== 游戏状态 =====================
let gameState = 'menu'; // menu | playing | over
let score     = 0;
let timeLeft  = GAME_DURATION;
let absorbCount = 0;
let lastTime  = 0;
let timerAcc  = 0;
let absorbedTypes = new Set(); // 记录已吞噬过的物品类型（用于胜利判定）
let gemSpawnAcc = 0;           // 宝石生成计时器
let edgeRemovalAcc = 0;        // 边缘建筑移除计时器
let edgeRemovalActive = false; // 边缘建筑移除是否已激活
let speedDebuffTimer  = 0;     // 黑洞速度减益剩余时间（秒）

// ===================== 输入系统 =====================
const keys = {};
window.addEventListener('keydown', (e) => {
  keys[e.key.toLowerCase()] = true;
  // 空格键重新开始（胜利或失败后均可触发）
  if (e.key === ' ' && gameState === 'over') {
    e.preventDefault();
    startGame();
  }
});
window.addEventListener('keyup', (e) => {
  keys[e.key.toLowerCase()] = false;
});

// ===================== 黑洞对象 =====================
const blackHole = {
  x: WORLD_W / 2,
  y: WORLD_H / 2,
  radius: 20,
  speed: BASE_SPEED,
  rotation: 0,          // 光晕旋转角度
  vx: 0,
  vy: 0,

  /** 根据输入更新黑洞位置 */
  update(dt) {
    let dx = 0, dy = 0;
    if (keys['w'] || keys['arrowup'])    dy -= 1;
    if (keys['s'] || keys['arrowdown'])  dy += 1;
    if (keys['a'] || keys['arrowleft'])  dx -= 1;
    if (keys['d'] || keys['arrowright']) dx += 1;

    // 对角移动归一化
    const len = Math.sqrt(dx * dx + dy * dy);
    if (len > 0) {
      dx /= len;
      dy /= len;
    }

    // 速度减益衰减
    if (speedDebuffTimer > 0) speedDebuffTimer = Math.max(0, speedDebuffTimer - dt);
    const effectiveSpeed = this.speed * (speedDebuffTimer > 0 ? PENALTY_SPEED_MULT : 1);

    // 平滑移动（带惯性）
    this.vx += (dx * effectiveSpeed - this.vx) * 0.15;
    this.vy += (dy * effectiveSpeed - this.vy) * 0.15;
    this.x += this.vx;
    this.y += this.vy;

    // 限制在世界边界内
    this.x = Math.max(this.radius, Math.min(WORLD_W - this.radius, this.x));
    this.y = Math.max(this.radius, Math.min(WORLD_H - this.radius, this.y));

    // 旋转光晕
    this.rotation += 0.02 + this.radius * 0.0001;
  },

  /** 吞噬减分建筑时应用惩罚 */
  applyPenalty() {
    score = Math.max(0, score - PENALTY_SCORE);
    this.radius *= PENALTY_RADIUS_SHRINK;
    this.speed = Math.max(MIN_SPEED, BASE_SPEED * Math.pow(SPEED_DECAY, this.radius - 20));
    speedDebuffTimer = PENALTY_DEBUFF_TIME;
  },

  /** 吞噬物品后增长 */
  grow(itemSize, itemScore) {
    const gain = itemSize * GROWTH_RATE;
    this.radius += gain;
    // 速度随体积增大而降低
    this.speed = Math.max(MIN_SPEED, BASE_SPEED * Math.pow(SPEED_DECAY, this.radius - 20));
    score += itemScore;
    absorbCount++;
  },

  /** 获取当前引力范围 */
  getGravityRange() {
    return this.radius * GRAVITY_FACTOR;
  }
};

// ===================== 相机系统 =====================
const camera = {
  x: 0,
  y: 0,
  shakeX: 0,
  shakeY: 0,
  shakeIntensity: 0,

  /** 跟随黑洞，并处理屏幕震动 */
  update() {
    // 平滑跟随
    const targetX = blackHole.x - canvas.width / 2;
    const targetY = blackHole.y - canvas.height / 2;
    this.x += (targetX - this.x) * 0.08;
    this.y += (targetY - this.y) * 0.08;

    // 限制相机范围
    this.x = Math.max(0, Math.min(WORLD_W - canvas.width, this.x));
    this.y = Math.max(0, Math.min(WORLD_H - canvas.height, this.y));

    // 震动衰减
    if (this.shakeIntensity > 0.1) {
      this.shakeX = (Math.random() - 0.5) * this.shakeIntensity;
      this.shakeY = (Math.random() - 0.5) * this.shakeIntensity;
      this.shakeIntensity *= 0.9;
    } else {
      this.shakeX = 0;
      this.shakeY = 0;
      this.shakeIntensity = 0;
    }
  },

  /** 触发屏幕震动 */
  shake(intensity) {
    this.shakeIntensity = Math.max(this.shakeIntensity, intensity);
  }
};

// ===================== 路网工具函数 =====================

/** 坐标是否在任意道路上 */
function isOnAnyRoad(x, y) {
  return isOnAnyH(x, y) || isOnAnyV(x, y);
}

function isOnAnyH(x, y) {
  for (const ry of MAIN_H_ROADS) if (Math.abs(y - ry) < MAIN_ROAD_W / 2) return true;
  for (const ry of SIDE_H_ROADS) if (Math.abs(y - ry) < SIDE_ROAD_W / 2) return true;
  return false;
}

function isOnAnyV(x, y) {
  for (const rx of MAIN_V_ROADS) if (Math.abs(x - rx) < MAIN_ROAD_W / 2) return true;
  for (const rx of SIDE_V_ROADS) if (Math.abs(x - rx) < SIDE_ROAD_W / 2) return true;
  return false;
}

/** 是否在路口 */
function isAtIntersection(x, y) {
  let nearH = false, nearV = false;
  for (const ry of ALL_H_ROADS) {
    if (Math.abs(y - ry) < INTERSECT_TOL) { nearH = true; break; }
  }
  if (!nearH) return false;
  for (const rx of ALL_V_ROADS) {
    if (Math.abs(x - rx) < INTERSECT_TOL) { nearV = true; break; }
  }
  return nearV;
}

/** 是否在街区内部（远离所有道路） */
function isInsideBlock(x, y) {
  const margin = 25;
  for (const ry of MAIN_H_ROADS) if (Math.abs(y - ry) < MAIN_ROAD_W / 2 + margin) return false;
  for (const ry of SIDE_H_ROADS) if (Math.abs(y - ry) < SIDE_ROAD_W / 2 + margin) return false;
  for (const rx of MAIN_V_ROADS) if (Math.abs(x - rx) < MAIN_ROAD_W / 2 + margin) return false;
  for (const rx of SIDE_V_ROADS) if (Math.abs(x - rx) < SIDE_ROAD_W / 2 + margin) return false;
  return true;
}

/** 道路上随机点 */
function getRandomOnRoad() {
  for (let i = 0; i < 300; i++) {
    const x = 30 + Math.random() * (WORLD_W - 60);
    const y = 30 + Math.random() * (WORLD_H - 60);
    if (isOnAnyRoad(x, y)) return { x, y };
  }
  return { x: WORLD_W / 2, y: MAIN_H_ROADS[0] };
}

/** 指定横向道路上随机点 */
function getRandomOnHRoad() {
  const ry = ALL_H_ROADS[Math.floor(Math.random() * ALL_H_ROADS.length)];
  return { x: 50 + Math.random() * (WORLD_W - 100), y: ry };
}

/** 指定纵向道路上随机点 */
function getRandomOnVRoad() {
  const rx = ALL_V_ROADS[Math.floor(Math.random() * ALL_V_ROADS.length)];
  return { x: rx, y: 50 + Math.random() * (WORLD_H - 100) };
}

/** 路边随机点（人行道位置） */
function getRandomRoadside() {
  const horizontal = Math.random() > 0.5;
  if (horizontal) {
    const ry = ALL_H_ROADS[Math.floor(Math.random() * ALL_H_ROADS.length)];
    const isMain = MAIN_H_ROADS.includes(ry);
    const offset = (isMain ? MAIN_ROAD_W : SIDE_ROAD_W) / 2 + 10;
    const side = Math.random() > 0.5 ? 1 : -1;
    return {
      x: 50 + Math.random() * (WORLD_W - 100),
      y: ry + side * offset
    };
  } else {
    const rx = ALL_V_ROADS[Math.floor(Math.random() * ALL_V_ROADS.length)];
    const isMain = MAIN_V_ROADS.includes(rx);
    const offset = (isMain ? MAIN_ROAD_W : SIDE_ROAD_W) / 2 + 10;
    const side = Math.random() > 0.5 ? 1 : -1;
    return {
      x: rx + side * offset,
      y: 50 + Math.random() * (WORLD_H - 100)
    };
  }
}

/** 街区内随机点 */
function getRandomInBlock() {
  for (let i = 0; i < 300; i++) {
    const x = 50 + Math.random() * (WORLD_W - 100);
    const y = 50 + Math.random() * (WORLD_H - 100);
    if (isInsideBlock(x, y)) return { x, y };
  }
  return { x: 200, y: 200 };
}

/** 十字路口随机点（仅主干道交叉口） */
function getRandomIntersection() {
  const hx = MAIN_V_ROADS[Math.floor(Math.random() * MAIN_V_ROADS.length)];
  const hy = MAIN_H_ROADS[Math.floor(Math.random() * MAIN_H_ROADS.length)];
  return { x: hx, y: hy };
}

/** 预计算街区矩形（用于渲染） */
function computeBlockRects() {
  const blocks = [];
  const hEdges = [0, ...ALL_H_ROADS, WORLD_H];
  const vEdges = [0, ...ALL_V_ROADS, WORLD_W];

  for (let i = 0; i < hEdges.length - 1; i++) {
    for (let j = 0; j < vEdges.length - 1; j++) {
      const y1 = hEdges[i], y2 = hEdges[i + 1];
      const x1 = vEdges[j], x2 = vEdges[j + 1];

      // 跳过道路所在区域
      let isRoad = false;
      for (const ry of ALL_H_ROADS) {
        const hw = MAIN_H_ROADS.includes(ry) ? MAIN_ROAD_W / 2 : SIDE_ROAD_W / 2;
        if (y1 >= ry - hw - 5 && y1 <= ry + hw + 5) { isRoad = true; break; }
      }
      if (!isRoad) {
        for (const rx of ALL_V_ROADS) {
          const hw = MAIN_V_ROADS.includes(rx) ? MAIN_ROAD_W / 2 : SIDE_ROAD_W / 2;
          if (x1 >= rx - hw - 5 && x1 <= rx + hw + 5) { isRoad = true; break; }
        }
      }
      if (isRoad) continue;

      // 计算街区内边界（去除路边人行道区域）
      let bx1 = x1, by1 = y1, bx2 = x2, by2 = y2;
      for (const ry of ALL_H_ROADS) {
        const hw = MAIN_H_ROADS.includes(ry) ? MAIN_ROAD_W / 2 : SIDE_ROAD_W / 2;
        if (Math.abs(y1 - (ry + hw)) < 15) by1 = ry + hw + 4;
        if (Math.abs(y2 - (ry - hw)) < 15) by2 = ry - hw - 4;
      }
      for (const rx of ALL_V_ROADS) {
        const hw = MAIN_V_ROADS.includes(rx) ? MAIN_ROAD_W / 2 : SIDE_ROAD_W / 2;
        if (Math.abs(x1 - (rx + hw)) < 15) bx1 = rx + hw + 4;
        if (Math.abs(x2 - (rx - hw)) < 15) bx2 = rx - hw - 4;
      }

      if (bx2 - bx1 > 30 && by2 - by1 > 30) {
        blocks.push({ x: bx1, y: by1, w: bx2 - bx1, h: by2 - by1 });
      }
    }
  }
  return blocks;
}

let blockRects = [];

// ===================== 物品系统 =====================

/** 物品类型定义 */
const ITEM_TYPES = {
  // 小型物品 - 容易吞噬，分数低
  person:    { category: 'small',  baseSize: 4,  score: 5,   color: '#ffcc80', minRadius: 0 },
  trash:     { category: 'small',  baseSize: 5,  score: 3,   color: '#8d6e63', minRadius: 0 },
  bush:      { category: 'small',  baseSize: 6,  score: 4,   color: '#66bb6a', minRadius: 0 },
  bench:     { category: 'small',  baseSize: 5,  score: 4,   color: '#a1887f', minRadius: 0 },

  // 中型物品 - 需要黑洞一定大小
  car:       { category: 'medium', baseSize: 12, score: 15,  color: '#ef5350', minRadius: 15 },
  lamppost:  { category: 'medium', baseSize: 10, score: 12,  color: '#ffd54f', minRadius: 12 },
  tree:      { category: 'medium', baseSize: 14, score: 18,  color: '#43a047', minRadius: 14 },
  fence:     { category: 'medium', baseSize: 8,  score: 8,   color: '#bcaaa4', minRadius: 10 },

  // 限时高价值物品
  gem:       { category: 'medium', baseSize: 15, score: 150, color: '#e040fb', minRadius: 0, isLimited: true },

  // 大型物品 - 需要很大的黑洞
  house:     { category: 'large',  baseSize: 30, score: 50,  color: '#78909c', minRadius: 28 },
  building:  { category: 'large',  baseSize: 50, score: 100, color: '#546e7a', minRadius: 40 },
  skyscraper:{ category: 'large',  baseSize: 70, score: 200, color: '#37474f', minRadius: 55 },
  bridge:    { category: 'large',  baseSize: 90, score: 350, color: '#455a64', minRadius: 70 },
};

/** 所有物品类型的 key 数组（用于胜利判定） */
const ALL_TYPE_KEYS = Object.keys(ITEM_TYPES);
const TOTAL_TYPE_COUNT = ALL_TYPE_KEYS.length; // 12

/** 物品数组 */
let items = [];

/** 生成一个物品 */
function spawnItem(typeKey) {
  const def = ITEM_TYPES[typeKey];
  const sizeVar = 0.8 + Math.random() * 0.4; // 大小随机浮动 ±20%
  const size = def.baseSize * sizeVar;
  let x, y;

  // ★ 根据物品类型决定放置位置
  switch (typeKey) {
    case 'car': {
      // 汽车只在路上，随机选择横向或纵向道路
      if (Math.random() > 0.5) {
        const pos = getRandomOnHRoad();
        x = pos.x; y = pos.y;
      } else {
        const pos = getRandomOnVRoad();
        x = pos.x; y = pos.y;
      }
      break;
    }
    case 'lamppost': {
      // 路灯沿路边放置
      const pos = getRandomRoadside();
      x = pos.x; y = pos.y;
      break;
    }
    case 'tree': {
      // 树木沿路边放置
      const pos = getRandomRoadside();
      x = pos.x; y = pos.y;
      break;
    }
    case 'house': case 'building': case 'skyscraper': {
      // 建筑在街区内
      const pos = getRandomInBlock();
      x = pos.x; y = pos.y;
      break;
    }
    case 'bridge': {
      // 桥只出现在主干道十字路口
      const pos = getRandomIntersection();
      x = pos.x; y = pos.y;
      break;
    }
    default: {
      // 行人/垃圾/灌木/长椅：街区内
      const pos = getRandomInBlock();
      x = pos.x; y = pos.y;
      break;
    }
  }

  const item = {
    type: typeKey,
    x: x,
    y: y,
    size: size,
    score: Math.round(def.score * sizeVar),
    color: def.color,
    category: def.category,
    minRadius: def.minRadius,
    // 物理状态
    vx: 0,
    vy: 0,
    rotation: 0,
    rotSpeed: (Math.random() - 0.5) * 0.1,
    // 吸附状态
    attracted: false,
    absorbed: false,
    alpha: 1,
    // 车辆特殊逻辑
    moveDir: 0,
    moveSpeed: 0,
    roadDir: null,       // 'h' 或 'v'，标记车辆所在道路方向
    turnCooldown: 0,     // 转弯冷却，防止路口反复转向
  };

  // 汽车初始化移动方向和速度
  if (typeKey === 'car') {
    item.moveSpeed = 0.5 + Math.random() * 1.5;
    item.moveDir = Math.random() > 0.5 ? 1 : -1;
    // 判断初始道路方向
    const onH = isOnAnyH(x, y);
    const onV = isOnAnyV(x, y);
    if (onH && !onV) {
      item.roadDir = 'h';
    } else if (onV && !onH) {
      item.roadDir = 'v';
    } else {
      // 在路口，随机选一个方向
      item.roadDir = Math.random() > 0.5 ? 'h' : 'v';
    }
  }

  // ★ 预生成窗户亮灯图案（避免每帧 Math.random() 导致窗户闪烁）
  if (typeKey === 'building') {
    item.windowMap = [];
    for (let r = 0; r < 5; r++) {
      item.windowMap[r] = [];
      for (let c = 0; c < 3; c++) item.windowMap[r][c] = Math.random() > 0.3;
    }
  } else if (typeKey === 'skyscraper') {
    item.windowMap = [];
    for (let r = 0; r < 8; r++) {
      item.windowMap[r] = [];
      for (let c = 0; c < 3; c++) item.windowMap[r][c] = Math.random() > 0.25;
    }
  } else if (typeKey === 'house') {
    item.windowLit = [Math.random() > 0.4, Math.random() > 0.4];
  }

  items.push(item);
}

/** 初始化城市物品分布 */
function populateCity() {
  items = [];

  // 小型物品：大量分布
  for (let i = 0; i < 80; i++) spawnItem('person');
  for (let i = 0; i < 40; i++) spawnItem('trash');
  for (let i = 0; i < 50; i++) spawnItem('bush');
  for (let i = 0; i < 30; i++) spawnItem('bench');

  // 中型物品
  for (let i = 0; i < 35; i++) spawnItem('car');
  for (let i = 0; i < 30; i++) spawnItem('lamppost');
  for (let i = 0; i < 40; i++) spawnItem('tree');
  for (let i = 0; i < 20; i++) spawnItem('fence');

  // 大型物品
  for (let i = 0; i < 20; i++) spawnItem('house');
  for (let i = 0; i < 12; i++) spawnItem('building');
  for (let i = 0; i < 6;  i++) spawnItem('skyscraper');
  for (let i = 0; i < 3;  i++) spawnItem('bridge');

  // 减分建筑（在所有普通物品生成后，避免重叠检测）
  spawnPenaltyBuildings();
}

/** 生成限时高价值宝石 */
function spawnGem() {
  const def = ITEM_TYPES.gem;
  const sizeVar = 0.8 + Math.random() * 0.4;
  const size = def.baseSize * sizeVar;

  // 在地图中部区域生成（远离边缘350px）
  let x, y;
  for (let i = 0; i < 100; i++) {
    x = EDGE_MARGIN + 50 + Math.random() * (WORLD_W - 2 * EDGE_MARGIN - 100);
    y = EDGE_MARGIN + 50 + Math.random() * (WORLD_H - 2 * EDGE_MARGIN - 100);
    if (!isOnAnyRoad(x, y)) break;
  }

  items.push({
    type: 'gem',
    x: x,
    y: y,
    size: size,
    score: Math.round(def.score * sizeVar),
    color: def.color,
    category: def.category,
    minRadius: def.minRadius,
    // 物理状态
    vx: 0,
    vy: 0,
    rotation: 0,
    rotSpeed: 0.04,
    // 吸附状态
    attracted: false,
    absorbed: false,
    alpha: 1,
    // 限时属性
    isLimited: true,
    timeLeft: GEM_LIFETIME,
    // 车辆特殊逻辑（宝石不需要）
    moveDir: 0,
    moveSpeed: 0,
    roadDir: null,
    turnCooldown: 0,
  });
}

/** 游戏过半后移除地图边缘建筑 */
function updateEdgeRemoval(dt) {
  const elapsed = GAME_DURATION - timeLeft;
  if (elapsed < GAME_DURATION / 2) return;
  if (!edgeRemovalActive) {
    edgeRemovalActive = true;
    edgeRemovalAcc = 0;
  }

  edgeRemovalAcc += dt;
  if (edgeRemovalAcc >= EDGE_REMOVAL_INTERVAL) {
    edgeRemovalAcc -= EDGE_REMOVAL_INTERVAL;

    // 收集所有边缘建筑
    const edgeBuildings = items.filter(item =>
      (item.type === 'house' || item.type === 'building' || item.type === 'skyscraper') &&
      (item.x < EDGE_MARGIN || item.x > WORLD_W - EDGE_MARGIN ||
       item.y < EDGE_MARGIN || item.y > WORLD_H - EDGE_MARGIN) &&
      !item.attracted
    );

    if (edgeBuildings.length > 0) {
      const target = edgeBuildings[Math.floor(Math.random() * edgeBuildings.length)];
      const idx = items.indexOf(target);
      if (idx !== -1) {
        // 消失粒子效果（灰尘）
        spawnAbsorbParticles(target.x, target.y, '#8d8d8d', 15);
        items.splice(idx, 1);
      }
    }
  }
}

/** 生成减分建筑（深红色危险建筑，吞噬会受罚） */
function spawnPenaltyBuildings() {
  const count = 1 + Math.floor(Math.random() * PENALTY_BUILDING_MAX); // 1~2个

  for (let n = 0; n < count; n++) {
    let x, y, valid;
    let attempts = 0;

    // 在地图边缘寻找不与其它建筑重叠的位置
    do {
      valid = true;
      // 随机选一条边缘（上下左右）
      const edge = Math.floor(Math.random() * 4);
      const margin = EDGE_MARGIN * 0.6;
      if (edge === 0) {        // 上边
        x = margin + Math.random() * (WORLD_W - margin * 2);
        y = margin * 0.5 + Math.random() * margin * 0.5;
      } else if (edge === 1) { // 下边
        x = margin + Math.random() * (WORLD_W - margin * 2);
        y = WORLD_H - margin * 0.5 - Math.random() * margin * 0.5;
      } else if (edge === 2) { // 左边
        x = margin * 0.5 + Math.random() * margin * 0.5;
        y = margin + Math.random() * (WORLD_H - margin * 2);
      } else {                 // 右边
        x = WORLD_W - margin * 0.5 - Math.random() * margin * 0.5;
        y = margin + Math.random() * (WORLD_H - margin * 2);
      }

      // 检测是否与已有大型建筑重叠
      const minDist = PENALTY_BUILDING_SIZE * 1.8;
      for (const other of items) {
        if (other.category !== 'large' && other.type !== 'penalty_building') continue;
        const dx = other.x - x;
        const dy = other.y - y;
        if (Math.sqrt(dx * dx + dy * dy) < minDist + other.size) {
          valid = false;
          break;
        }
      }
      attempts++;
    } while (!valid && attempts < 30);

    if (!valid) continue; // 找不到合适位置则跳过

    const sizeVar = 0.95 + Math.random() * 0.1; // 大小随机浮动 ±5%
    const size = PENALTY_BUILDING_SIZE * sizeVar;

    items.push({
      type: 'penalty_building',
      x: x,
      y: y,
      size: size,
      score: 0,            // 吞噬时不计正常分数，单独扣分
      color: '#8b0000',
      category: 'large',
      minRadius: 80,       // 需要非常大的黑洞才能吞噬
      // 物理状态
      vx: 0,
      vy: 0,
      rotation: 0,
      rotSpeed: 0,
      // 吸附状态
      attracted: false,
      absorbed: false,
      alpha: 1,
      // 脉冲动画相位
      pulsePhase: Math.random() * Math.PI * 2,
      // 窗户图案
      windowMap: (() => {
        const map = [];
        for (let r = 0; r < 8; r++) {
          map[r] = [];
          for (let c = 0; c < 4; c++) map[r][c] = Math.random() > 0.5;
        }
        return map;
      })(),
      // 车辆特殊逻辑（不需要）
      moveDir: 0,
      moveSpeed: 0,
      roadDir: null,
      turnCooldown: 0,
    });
  }
}

// ===================== 粒子系统 =====================
let particles = [];

/** 创建吞噬粒子效果 */
function spawnAbsorbParticles(x, y, color, count) {
  const isRainbow = score >= RAINBOW_SCORE;
  for (let i = 0; i < count; i++) {
    const angle = Math.random() * Math.PI * 2;
    const speed = 1 + Math.random() * 3;
    const particleColor = isRainbow
      ? rainbowColor(Math.random() * 360)
      : color;
    particles.push({
      x: x + (Math.random() - 0.5) * 20,
      y: y + (Math.random() - 0.5) * 20,
      vx: Math.cos(angle) * speed,
      vy: Math.sin(angle) * speed,
      life: 1,
      decay: 0.015 + Math.random() * 0.025,
      size: 2 + Math.random() * 4,
      color: particleColor,
    });
  }
}

/** 更新粒子 */
function updateParticles() {
  for (let i = particles.length - 1; i >= 0; i--) {
    const p = particles[i];
    // 粒子向黑洞中心聚拢
    const dx = blackHole.x - p.x;
    const dy = blackHole.y - p.y;
    const dist = Math.sqrt(dx * dx + dy * dy) || 1;
    p.vx += (dx / dist) * 0.08;
    p.vy += (dy / dist) * 0.08;
    p.x  += p.vx;
    p.y  += p.vy;
    p.life -= p.decay;
    if (p.life <= 0) {
      particles.splice(i, 1);
    }
  }
}

// ===================== 星空背景 =====================
let stars = [];
function initStars() {
  stars = [];
  for (let i = 0; i < 200; i++) {
    stars.push({
      x: Math.random() * WORLD_W,
      y: Math.random() * WORLD_H,
      size: 0.5 + Math.random() * 2,
      twinkle: Math.random() * Math.PI * 2, // 闪烁相位
    });
  }
}
initStars();

// ===================== 物品物理与碰撞 =====================
function updateItems(dt) {
  const gravRange = blackHole.getGravityRange();

  for (let i = items.length - 1; i >= 0; i--) {
    const item = items[i];

    // --- 车辆沿道路行驶 ---
    if (item.moveDir !== 0 && !item.attracted) {
      // 转弯冷却
      if (item.turnCooldown > 0) item.turnCooldown--;

      // 在路口且冷却结束：可随机变道
      if (item.turnCooldown <= 0 && isAtIntersection(item.x, item.y)) {
        if (Math.random() < 0.25) {
          // 切换道路方向
          item.roadDir = item.roadDir === 'h' ? 'v' : 'h';
          item.turnCooldown = 40;
        }
      }

      // 沿道路方向移动，锁定在道路中心线上
      if (item.roadDir === 'h') {
        item.x += item.moveDir * item.moveSpeed;
        // 到达世界边缘掉头
        if (item.x < 30 || item.x > WORLD_W - 30) {
          item.moveDir *= -1;
        }
      } else {
        item.y += item.moveDir * item.moveSpeed;
        // 到达世界边缘掉头
        if (item.y < 30 || item.y > WORLD_H - 30) {
          item.moveDir *= -1;
        }
      }
    }

    // --- 引力吸附逻辑 ---
    const dx = blackHole.x - item.x;
    const dy = blackHole.y - item.y;
    const dist = Math.sqrt(dx * dx + dy * dy) || 1;

    if (dist < gravRange && blackHole.radius >= item.minRadius) {
      item.attracted = true;
      // 引力强度随距离衰减
      const force = PULL_STRENGTH * (1 - dist / gravRange);
      item.vx += (dx / dist) * force;
      item.vy += (dy / dist) * force;
      // 被吸引时旋转加速
      item.rotSpeed += 0.005;
    }

    // --- 减分建筑斥力场（推开靠近的黑洞） ---
    if (item.type === 'penalty_building' && dist < PENALTY_REPEL_RANGE && !item.attracted) {
      const repelStrength = PENALTY_REPEL_FORCE * (1 - dist / PENALTY_REPEL_RANGE);
      // 推力方向：从建筑指向黑洞（推开黑洞）
      blackHole.vx += (dx / dist) * repelStrength;
      blackHole.vy += (dy / dist) * repelStrength;
    }

    // 应用速度
    if (item.attracted) {
      item.x += item.vx;
      item.y += item.vy;
      item.rotation += item.rotSpeed;
      // 摩擦
      item.vx *= 0.98;
      item.vy *= 0.98;
    }

    // --- 限时物品倒计时 ---
    if (item.isLimited) {
      item.timeLeft -= dt;
      // 更新闪烁透明度（剩余时间越少闪烁越快）
      const flashSpeed = item.timeLeft > 2 ? 4 : 10;
      item.alpha = 0.35 + 0.65 * (0.5 + 0.5 * Math.sin(item.timeLeft * flashSpeed));

      if (item.timeLeft <= 0) {
        // 消失惩罚：扣除分数
        const penalty = Math.round(item.score * 0.5);
        score = Math.max(0, score - penalty);
        // 消失粒子（红色碎裂效果）
        spawnAbsorbParticles(item.x, item.y, '#ff5252', 18);
        items.splice(i, 1);
        continue;
      }
    }

    // --- 吞噬检测 ---
    if (dist < blackHole.radius * ABSORB_RATIO && blackHole.radius >= item.minRadius) {
      // ★ 减分建筑特殊处理：施加惩罚，不执行正常吞噬流程
      if (item.type === 'penalty_building') {
        camera.shake(item.size * 0.8);
        spawnAbsorbParticles(item.x, item.y, '#ff0000', 35);
        spawnAbsorbParticles(item.x, item.y, '#8b0000', 20);
        blackHole.applyPenalty();
        items.splice(i, 1);
        continue;
      }
      // 大型物品触发屏幕震动
      if (item.size > SHAKE_THRESHOLD) {
        camera.shake(item.size * 0.5);
      }
      // 生成粒子效果
      const particleCount = item.category === 'large' ? 25 : item.category === 'medium' ? 12 : 6;
      spawnAbsorbParticles(item.x, item.y, item.color, particleCount);
      // 黑洞增长
      blackHole.grow(item.size, item.score);
      // ★ 记录该物品类型已被吞噬（用于胜利判定）
      absorbedTypes.add(item.type);
      // 移除物品
      items.splice(i, 1);
    }
  }

  // ★ 胜利判定：所有物品类型都至少吞噬过 1 种，且场上已无可吞噬物品
  if (items.length === 0 && absorbedTypes.size >= TOTAL_TYPE_COUNT) {
    endGame(true);
  }
}

// ===================== 渲染系统 =====================

/** 绘制城市地面（现代化密集路网） */
function drawGround() {
  // 1. 基础地面（草地/泥土）
  ctx.fillStyle = '#2d4a3e';
  ctx.fillRect(0, 0, WORLD_W, WORLD_H);

  // 2. 街区填充（浅灰人行道区域）
  for (const b of blockRects) {
    ctx.fillStyle = '#4a4f4a';
    ctx.fillRect(b.x, b.y, b.w, b.h);
  }

  // 3. 绘制所有道路路面
  ctx.fillStyle = '#3a3a4a';
  // 横向道路
  for (const ry of MAIN_H_ROADS) {
    ctx.fillRect(0, ry - MAIN_ROAD_W / 2, WORLD_W, MAIN_ROAD_W);
  }
  for (const ry of SIDE_H_ROADS) {
    ctx.fillRect(0, ry - SIDE_ROAD_W / 2, WORLD_W, SIDE_ROAD_W);
  }
  // 纵向道路
  for (const rx of MAIN_V_ROADS) {
    ctx.fillRect(rx - MAIN_ROAD_W / 2, 0, MAIN_ROAD_W, WORLD_H);
  }
  for (const rx of SIDE_V_ROADS) {
    ctx.fillRect(rx - SIDE_ROAD_W / 2, 0, SIDE_ROAD_W, WORLD_H);
  }

  // 4. 人行道边缘线（道路与街区的分界）
  ctx.strokeStyle = '#6a6a5a';
  ctx.lineWidth = 1;
  for (const ry of MAIN_H_ROADS) {
    ctx.beginPath();
    ctx.moveTo(0, ry - MAIN_ROAD_W / 2);
    ctx.lineTo(WORLD_W, ry - MAIN_ROAD_W / 2);
    ctx.moveTo(0, ry + MAIN_ROAD_W / 2);
    ctx.lineTo(WORLD_W, ry + MAIN_ROAD_W / 2);
    ctx.stroke();
  }
  for (const ry of SIDE_H_ROADS) {
    ctx.beginPath();
    ctx.moveTo(0, ry - SIDE_ROAD_W / 2);
    ctx.lineTo(WORLD_W, ry - SIDE_ROAD_W / 2);
    ctx.moveTo(0, ry + SIDE_ROAD_W / 2);
    ctx.lineTo(WORLD_W, ry + SIDE_ROAD_W / 2);
    ctx.stroke();
  }
  for (const rx of MAIN_V_ROADS) {
    ctx.beginPath();
    ctx.moveTo(rx - MAIN_ROAD_W / 2, 0);
    ctx.lineTo(rx - MAIN_ROAD_W / 2, WORLD_H);
    ctx.moveTo(rx + MAIN_ROAD_W / 2, 0);
    ctx.lineTo(rx + MAIN_ROAD_W / 2, WORLD_H);
    ctx.stroke();
  }
  for (const rx of SIDE_V_ROADS) {
    ctx.beginPath();
    ctx.moveTo(rx - SIDE_ROAD_W / 2, 0);
    ctx.lineTo(rx - SIDE_ROAD_W / 2, WORLD_H);
    ctx.moveTo(rx + SIDE_ROAD_W / 2, 0);
    ctx.lineTo(rx + SIDE_ROAD_W / 2, WORLD_H);
    ctx.stroke();
  }

  // 5. 主干道中线（黄色虚线）
  ctx.strokeStyle = '#ffd54f55';
  ctx.lineWidth = 2;
  ctx.setLineDash([20, 15]);
  for (const ry of MAIN_H_ROADS) {
    ctx.beginPath();
    ctx.moveTo(0, ry);
    ctx.lineTo(WORLD_W, ry);
    ctx.stroke();
  }
  for (const rx of MAIN_V_ROADS) {
    ctx.beginPath();
    ctx.moveTo(rx, 0);
    ctx.lineTo(rx, WORLD_H);
    ctx.stroke();
  }
  ctx.setLineDash([]);

  // 6. 小马路中线（白色虚线）
  ctx.strokeStyle = 'rgba(255,255,255,0.15)';
  ctx.lineWidth = 1;
  ctx.setLineDash([10, 10]);
  for (const ry of SIDE_H_ROADS) {
    ctx.beginPath();
    ctx.moveTo(0, ry);
    ctx.lineTo(WORLD_W, ry);
    ctx.stroke();
  }
  for (const rx of SIDE_V_ROADS) {
    ctx.beginPath();
    ctx.moveTo(rx, 0);
    ctx.lineTo(rx, WORLD_H);
    ctx.stroke();
  }
  ctx.setLineDash([]);

  // 7. 主干道十字路口斑马线
  for (const hy of MAIN_H_ROADS) {
    for (const vx of MAIN_V_ROADS) {
      const halfM = MAIN_ROAD_W / 2;
      // 上侧斑马线
      ctx.fillStyle = 'rgba(255,255,255,0.2)';
      for (let s = -halfM; s < halfM; s += 5) {
        ctx.fillRect(vx + s, hy - halfM - 8, 3, 8);
      }
      // 下侧斑马线
      for (let s = -halfM; s < halfM; s += 5) {
        ctx.fillRect(vx + s, hy + halfM, 3, 8);
      }
      // 左侧斑马线
      for (let s = -halfM; s < halfM; s += 5) {
        ctx.fillRect(vx - halfM - 8, hy + s, 8, 3);
      }
      // 右侧斑马线
      for (let s = -halfM; s < halfM; s += 5) {
        ctx.fillRect(vx + halfM, hy + s, 8, 3);
      }
    }
  }
}

/** 绘制星空（黑洞变大后出现，或彩虹模式） */
function drawStars() {
  const isRainbow = score >= RAINBOW_SCORE;
  if (blackHole.radius < STAR_THRESHOLD && !isRainbow) return;
  const baseAlpha = isRainbow
    ? 0.35
    : Math.min(1, (blackHole.radius - STAR_THRESHOLD) / 60);
  for (const star of stars) {
    star.twinkle += 0.03;
    const a = baseAlpha * (0.5 + 0.5 * Math.sin(star.twinkle));
    ctx.fillStyle = `rgba(255,255,255,${a})`;
    ctx.beginPath();
    ctx.arc(star.x, star.y, star.size, 0, Math.PI * 2);
    ctx.fill();
  }
}

/** 根据类型绘制单个物品 */
function drawItem(item) {
  ctx.save();
  ctx.translate(item.x, item.y);
  ctx.rotate(item.rotation);
  ctx.globalAlpha = item.alpha;

  const s = item.size;

  switch (item.type) {

    // ─── 小人：圆头 + 矩形身体 + 两条腿，暖色系 ───
    case 'person': {
      // 衣服颜色池（暖色系）
      const shirtColors = ['#e57373','#ffb74d','#fff176','#ff8a65','#f06292'];
      const shirt = shirtColors[Math.floor(item.x) % 5];

      // 头部（圆形）
      ctx.fillStyle = '#ffcc80';
      ctx.beginPath();
      ctx.arc(0, -s * 0.6, s * 0.35, 0, Math.PI * 2);
      ctx.fill();
      // 头发
      ctx.fillStyle = '#5d4037';
      ctx.beginPath();
      ctx.arc(0, -s * 0.75, s * 0.28, Math.PI, Math.PI * 2);
      ctx.fill();

      // 身体（矩形）
      ctx.fillStyle = shirt;
      ctx.fillRect(-s * 0.3, -s * 0.25, s * 0.6, s * 0.7);
      // 衣领
      ctx.fillStyle = shadeColor(shirt, -30);
      ctx.fillRect(-s * 0.15, -s * 0.25, s * 0.3, s * 0.1);

      // 腿（两条矩形）
      ctx.fillStyle = '#5d4037';
      ctx.fillRect(-s * 0.25, s * 0.45, s * 0.2, s * 0.5);
      ctx.fillRect(s * 0.05,  s * 0.45, s * 0.2, s * 0.5);

      // 手臂（短线）
      ctx.strokeStyle = shirt;
      ctx.lineWidth = Math.max(1, s * 0.12);
      ctx.lineCap = 'round';
      ctx.beginPath();
      ctx.moveTo(-s * 0.3, -s * 0.1);
      ctx.lineTo(-s * 0.48, s * 0.2);
      ctx.moveTo( s * 0.3, -s * 0.1);
      ctx.lineTo( s * 0.48, s * 0.2);
      ctx.stroke();
      break;
    }

    case 'trash':
      ctx.fillStyle = '#6d4c41';
      ctx.fillRect(-s * 0.4, -s * 0.5, s * 0.8, s);
      ctx.fillStyle = '#5d4037';
      ctx.fillRect(-s * 0.45, -s * 0.55, s * 0.9, s * 0.15);
      break;

    case 'bush':
      ctx.fillStyle = '#388e3c';
      ctx.beginPath();
      ctx.arc(0, 0, s * 0.5, 0, Math.PI * 2);
      ctx.fill();
      ctx.fillStyle = '#43a047';
      ctx.beginPath();
      ctx.arc(-s * 0.2, -s * 0.1, s * 0.35, 0, Math.PI * 2);
      ctx.fill();
      ctx.fillStyle = '#4caf50';
      ctx.beginPath();
      ctx.arc(s * 0.2, -s * 0.15, s * 0.3, 0, Math.PI * 2);
      ctx.fill();
      break;

    case 'bench':
      ctx.fillStyle = '#8d6e63';
      ctx.fillRect(-s * 0.6, -s * 0.1, s * 1.2, s * 0.2);
      ctx.fillStyle = '#6d4c41';
      ctx.fillRect(-s * 0.5, s * 0.1, s * 0.12, s * 0.4);
      ctx.fillRect(s * 0.38, s * 0.1, s * 0.12, s * 0.4);
      break;

    // ─── 汽车：圆角车身 + 圆形轮子 + 车顶 + 车灯 ───
    case 'car': {
      // 车身阴影
      ctx.fillStyle = 'rgba(0,0,0,0.15)';
      roundRect(-s * 0.58, -s * 0.15, s * 1.2, s * 0.55, 4);

      // 车身（圆角矩形）
      ctx.fillStyle = item.color;
      roundRect(-s * 0.6, -s * 0.2, s * 1.2, s * 0.5, 4);

      // 车顶
      ctx.fillStyle = shadeColor(item.color, -20);
      roundRect(-s * 0.3, -s * 0.45, s * 0.6, s * 0.3, 3);

      // 车窗
      ctx.fillStyle = '#b3e5fc';
      ctx.fillRect(-s * 0.22, -s * 0.4, s * 0.2, s * 0.2);
      ctx.fillRect( s * 0.02, -s * 0.4, s * 0.2, s * 0.2);

      // 车轮（前后各一，含轮毂）
      ctx.fillStyle = '#212121';
      ctx.beginPath();
      ctx.arc(-s * 0.35, s * 0.32, s * 0.13, 0, Math.PI * 2);
      ctx.arc( s * 0.35, s * 0.32, s * 0.13, 0, Math.PI * 2);
      ctx.fill();
      ctx.fillStyle = '#616161';
      ctx.beginPath();
      ctx.arc(-s * 0.35, s * 0.32, s * 0.05, 0, Math.PI * 2);
      ctx.arc( s * 0.35, s * 0.32, s * 0.05, 0, Math.PI * 2);
      ctx.fill();

      // 前车灯（黄色 + 发光）
      ctx.fillStyle = '#ffeb3b';
      ctx.beginPath();
      ctx.arc(s * 0.55, -s * 0.02, s * 0.07, 0, Math.PI * 2);
      ctx.fill();
      ctx.fillStyle = 'rgba(255,235,59,0.2)';
      ctx.beginPath();
      ctx.arc(s * 0.55, -s * 0.02, s * 0.15, 0, Math.PI * 2);
      ctx.fill();

      // 后尾灯（红色）
      ctx.fillStyle = '#f44336';
      ctx.beginPath();
      ctx.arc(-s * 0.55, -s * 0.02, s * 0.06, 0, Math.PI * 2);
      ctx.fill();
      break;
    }

    // ─── 路灯：细长杆 + 圆形灯泡 + 黄色光晕 ───
    case 'lamppost':
      // 灯杆底座
      ctx.fillStyle = '#616161';
      ctx.fillRect(-s * 0.15, s * 0.8, s * 0.3, s * 0.15);

      // 灯杆（细长）
      ctx.fillStyle = '#757575';
      ctx.fillRect(-s * 0.05, -s * 0.3, s * 0.1, s * 1.1);

      // 灯臂（弯曲支架）
      ctx.strokeStyle = '#757575';
      ctx.lineWidth = Math.max(1, s * 0.06);
      ctx.lineCap = 'round';
      ctx.beginPath();
      ctx.moveTo(0, -s * 0.25);
      ctx.quadraticCurveTo(s * 0.25, -s * 0.45, s * 0.15, -s * 0.55);
      ctx.stroke();

      // 灯泡外发光（大范围柔和光晕）
      ctx.fillStyle = 'rgba(255,213,79,0.08)';
      ctx.beginPath();
      ctx.arc(s * 0.15, -s * 0.55, s * 0.8, 0, Math.PI * 2);
      ctx.fill();
      // 中层光晕
      ctx.fillStyle = 'rgba(255,213,79,0.18)';
      ctx.beginPath();
      ctx.arc(s * 0.15, -s * 0.55, s * 0.4, 0, Math.PI * 2);
      ctx.fill();

      // 灯泡（黄色圆形）
      ctx.fillStyle = '#ffd54f';
      ctx.beginPath();
      ctx.arc(s * 0.15, -s * 0.55, s * 0.15, 0, Math.PI * 2);
      ctx.fill();
      // 灯泡高光
      ctx.fillStyle = '#fff9c4';
      ctx.beginPath();
      ctx.arc(s * 0.12, -s * 0.58, s * 0.06, 0, Math.PI * 2);
      ctx.fill();
      break;

    // ─── 树木：棕色树干 + 绿色三角树冠 + 树枝 ───
    case 'tree':
      // 树干
      ctx.fillStyle = '#5d4037';
      ctx.fillRect(-s * 0.08, s * 0.1, s * 0.16, s * 0.55);
      // 树干纹理
      ctx.strokeStyle = '#4e342e';
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.moveTo(-s * 0.02, s * 0.15);
      ctx.lineTo(-s * 0.02, s * 0.55);
      ctx.moveTo( s * 0.03, s * 0.25);
      ctx.lineTo( s * 0.03, s * 0.6);
      ctx.stroke();

      // 树枝（左右各一）
      ctx.strokeStyle = '#5d4037';
      ctx.lineWidth = Math.max(1, s * 0.05);
      ctx.lineCap = 'round';
      ctx.beginPath();
      ctx.moveTo(0, s * 0.15);
      ctx.lineTo(-s * 0.25, -s * 0.05);
      ctx.moveTo(0, s * 0.1);
      ctx.lineTo( s * 0.22, -s * 0.1);
      ctx.stroke();

      // 树冠底层（最深绿，最大三角）
      ctx.fillStyle = '#2e7d32';
      ctx.beginPath();
      ctx.moveTo(0, -s * 0.9);
      ctx.lineTo(-s * 0.55, s * 0.15);
      ctx.lineTo( s * 0.55, s * 0.15);
      ctx.closePath();
      ctx.fill();

      // 树冠中层
      ctx.fillStyle = '#388e3c';
      ctx.beginPath();
      ctx.moveTo(0, -s * 0.75);
      ctx.lineTo(-s * 0.45, s * 0.0);
      ctx.lineTo( s * 0.45, s * 0.0);
      ctx.closePath();
      ctx.fill();

      // 树冠顶层（最亮绿，最小三角）
      ctx.fillStyle = '#43a047';
      ctx.beginPath();
      ctx.moveTo(0, -s * 0.55);
      ctx.lineTo(-s * 0.3, -s * 0.1);
      ctx.lineTo( s * 0.3, -s * 0.1);
      ctx.closePath();
      ctx.fill();
      break;

    case 'fence':
      ctx.fillStyle = '#bcaaa4';
      // 横条
      ctx.fillRect(-s * 0.5, -s * 0.1, s, s * 0.08);
      ctx.fillRect(-s * 0.5, s * 0.1, s, s * 0.08);
      // 竖条
      for (let i = -0.4; i <= 0.4; i += 0.2) {
        ctx.fillRect(s * i - 1, -s * 0.25, 3, s * 0.55);
      }
      break;

    // ─── 小楼（house）：矮矩形 + 三角屋顶 + 烟囱 + 门窗 ───
    case 'house': {
      // 墙体
      ctx.fillStyle = item.color;
      ctx.fillRect(-s * 0.4, -s * 0.15, s * 0.8, s * 0.65);
      // 墙体底部阴影
      ctx.fillStyle = 'rgba(0,0,0,0.1)';
      ctx.fillRect(-s * 0.4, s * 0.3, s * 0.8, s * 0.2);

      // 三角屋顶
      ctx.fillStyle = '#c62828';
      ctx.beginPath();
      ctx.moveTo(0, -s * 0.55);
      ctx.lineTo(-s * 0.5, -s * 0.1);
      ctx.lineTo( s * 0.5, -s * 0.1);
      ctx.closePath();
      ctx.fill();
      // 屋顶高光
      ctx.fillStyle = '#d32f2f';
      ctx.beginPath();
      ctx.moveTo(0, -s * 0.55);
      ctx.lineTo(-s * 0.25, -s * 0.32);
      ctx.lineTo( s * 0.25, -s * 0.32);
      ctx.closePath();
      ctx.fill();

      // 烟囱
      ctx.fillStyle = '#795548';
      ctx.fillRect(s * 0.15, -s * 0.55, s * 0.1, s * 0.2);

      // 门
      ctx.fillStyle = '#5d4037';
      ctx.fillRect(-s * 0.08, s * 0.2, s * 0.16, s * 0.3);
      // 门把手
      ctx.fillStyle = '#ffd54f';
      ctx.beginPath();
      ctx.arc(s * 0.05, s * 0.36, s * 0.02, 0, Math.PI * 2);
      ctx.fill();

      // 窗户（白色方块，预生成亮灯状态）
      const wl = item.windowLit || [true, true];
      ctx.fillStyle = wl[0] ? '#fff9c4' : '#90a4ae';
      ctx.fillRect(-s * 0.32, s * 0.0, s * 0.15, s * 0.15);
      ctx.fillStyle = wl[1] ? '#fff9c4' : '#90a4ae';
      ctx.fillRect( s * 0.17, s * 0.0, s * 0.15, s * 0.15);
      // 窗框
      ctx.strokeStyle = '#455a64';
      ctx.lineWidth = 1;
      ctx.strokeRect(-s * 0.32, s * 0.0, s * 0.15, s * 0.15);
      ctx.strokeRect( s * 0.17, s * 0.0, s * 0.15, s * 0.15);
      break;
    }

    // ─── 高楼（building）：中高矩形 + 窗户矩阵 + 平顶檐口 ───
    case 'building': {
      // 主楼体
      ctx.fillStyle = item.color;
      ctx.fillRect(-s * 0.35, -s * 0.5, s * 0.7, s);

      // 屋顶檐口
      ctx.fillStyle = '#37474f';
      ctx.fillRect(-s * 0.38, -s * 0.52, s * 0.76, s * 0.04);
      // 屋顶水箱
      ctx.fillStyle = '#455a64';
      ctx.fillRect(-s * 0.1, -s * 0.62, s * 0.2, s * 0.1);
      ctx.fillStyle = '#37474f';
      ctx.fillRect(-s * 0.12, -s * 0.64, s * 0.24, s * 0.03);

      // 底部入口
      ctx.fillStyle = '#37474f';
      ctx.fillRect(-s * 0.08, s * 0.35, s * 0.16, s * 0.15);

      // 窗户矩阵（使用预生成的亮灯图案，避免每帧闪烁）
      const wCols = 3, wRows = 5;
      const ww = s * 0.12, wh = s * 0.1;
      const wMap = item.windowMap;
      for (let r = 0; r < wRows; r++) {
        for (let c = 0; c < wCols; c++) {
          const wx = -s * 0.25 + c * (s * 0.7 / wCols);
          const wy = -s * 0.4 + r * (s / wRows);
          ctx.fillStyle = (wMap && wMap[r][c]) ? '#fff9c4' : '#90a4ae';
          ctx.fillRect(wx, wy, ww, wh);
        }
      }
      break;
    }

    // ─── 大厦（skyscraper）：最高矩形 + 金属渐变 + 天线 + 装饰带 ───
    case 'skyscraper': {
      // 主楼（金属渐变）
      const grad = ctx.createLinearGradient(0, -s * 0.6, 0, s * 0.6);
      grad.addColorStop(0, '#263238');
      grad.addColorStop(1, item.color);
      ctx.fillStyle = grad;
      ctx.fillRect(-s * 0.25, -s * 0.55, s * 0.5, s * 1.1);

      // 尖顶天线
      ctx.fillStyle = '#90a4ae';
      ctx.fillRect(-s * 0.02, -s * 0.8, s * 0.04, s * 0.25);
      // 天线顶部红球
      ctx.fillStyle = '#f44336';
      ctx.beginPath();
      ctx.arc(0, -s * 0.82, s * 0.035, 0, Math.PI * 2);
      ctx.fill();
      // 红色警示灯光晕
      ctx.fillStyle = 'rgba(244,67,54,0.15)';
      ctx.beginPath();
      ctx.arc(0, -s * 0.82, s * 0.08, 0, Math.PI * 2);
      ctx.fill();

      // 屋顶装饰层
      ctx.fillStyle = '#37474f';
      ctx.fillRect(-s * 0.28, -s * 0.55, s * 0.56, s * 0.04);

      // 横向装饰带（每隔几层）
      ctx.fillStyle = '#455a64';
      for (let r = 0; r < 4; r++) {
        ctx.fillRect(-s * 0.25, -s * 0.35 + r * s * 0.24, s * 0.5, s * 0.02);
      }

      // 窗户（使用预生成图案）
      const sMap = item.windowMap;
      ctx.fillStyle = '#fff59d';
      for (let r = 0; r < 8; r++) {
        for (let c = 0; c < 3; c++) {
          if (sMap && sMap[r][c]) {
            ctx.fillRect(
              -s * 0.18 + c * s * 0.14,
              -s * 0.45 + r * s * 0.12,
              s * 0.08, s * 0.07
            );
          }
        }
      }

      // 底部大堂入口
      ctx.fillStyle = '#263238';
      ctx.fillRect(-s * 0.12, s * 0.42, s * 0.24, s * 0.13);
      // 大堂灯光
      ctx.fillStyle = '#fff9c4';
      ctx.fillRect(-s * 0.08, s * 0.44, s * 0.16, s * 0.06);
      break;
    }

    // ─── 减分建筑：深红色巨型建筑 + 红色脉冲光晕 + 警告标识 ───
    case 'penalty_building': {
      // 脉冲动画（放大缩小）
      item.pulsePhase += 0.06;
      const pulse = 1 + 0.08 * Math.sin(item.pulsePhase);
      const pulseAlpha = 0.5 + 0.5 * Math.sin(item.pulsePhase);

      // 外层大范围红色发光光晕（脉冲透明度）
      const outerGlow = ctx.createRadialGradient(0, 0, s * 0.3, 0, 0, s * 2.2);
      outerGlow.addColorStop(0, `rgba(220, 20, 20, ${0.35 * pulseAlpha})`);
      outerGlow.addColorStop(0.4, `rgba(180, 0, 0, ${0.2 * pulseAlpha})`);
      outerGlow.addColorStop(1, 'rgba(100, 0, 0, 0)');
      ctx.fillStyle = outerGlow;
      ctx.beginPath();
      ctx.arc(0, 0, s * 2.2, 0, Math.PI * 2);
      ctx.fill();

      // 中层脉冲光环（收缩扩散效果）
      ctx.strokeStyle = `rgba(255, 50, 50, ${0.6 * pulseAlpha})`;
      ctx.lineWidth = 3;
      ctx.beginPath();
      ctx.arc(0, 0, s * (1.3 + 0.3 * pulse), 0, Math.PI * 2);
      ctx.stroke();

      // 应用脉冲缩放（仅建筑本体）
      ctx.save();
      ctx.scale(pulse, pulse);

      // 主楼体（深红渐变）
      const bodyGrad = ctx.createLinearGradient(0, -s * 0.6, 0, s * 0.6);
      bodyGrad.addColorStop(0, '#4a0000');
      bodyGrad.addColorStop(0.5, '#8b0000');
      bodyGrad.addColorStop(1, '#3a0000');
      ctx.fillStyle = bodyGrad;
      ctx.fillRect(-s * 0.35, -s * 0.55, s * 0.7, s * 1.1);

      // 屋顶锯齿装饰（警告风格）
      ctx.fillStyle = '#ffcc00';
      const stripeCount = 5;
      const stripeW = s * 0.7 / stripeCount;
      for (let i = 0; i < stripeCount; i++) {
        if (i % 2 === 0) {
          ctx.fillRect(-s * 0.35 + i * stripeW, -s * 0.58, stripeW, s * 0.04);
        }
      }

      // 屋顶尖刺
      ctx.fillStyle = '#2a0000';
      ctx.beginPath();
      ctx.moveTo(-s * 0.3, -s * 0.55);
      ctx.lineTo(-s * 0.2, -s * 0.75);
      ctx.lineTo(-s * 0.1, -s * 0.55);
      ctx.closePath();
      ctx.fill();
      ctx.beginPath();
      ctx.moveTo(s * 0.1, -s * 0.55);
      ctx.lineTo(s * 0.2, -s * 0.75);
      ctx.lineTo(s * 0.3, -s * 0.55);
      ctx.closePath();
      ctx.fill();

      // 中央警告标志（红色三角 + 感叹号）
      ctx.fillStyle = '#1a0000';
      ctx.fillRect(-s * 0.15, -s * 0.2, s * 0.3, s * 0.4);
      ctx.fillStyle = '#ff3030';
      ctx.beginPath();
      ctx.moveTo(0, -s * 0.15);
      ctx.lineTo(s * 0.1, s * 0.08);
      ctx.lineTo(-s * 0.1, s * 0.08);
      ctx.closePath();
      ctx.fill();
      // 感叹号
      ctx.fillStyle = '#ffffff';
      ctx.fillRect(-s * 0.02, -s * 0.08, s * 0.04, s * 0.1);
      ctx.beginPath();
      ctx.arc(0, s * 0.06, s * 0.025, 0, Math.PI * 2);
      ctx.fill();

      // 窗户矩阵（红色调窗户）
      const ww = s * 0.1, wh = s * 0.08;
      const wMap = item.windowMap;
      for (let r = 0; r < 8; r++) {
        for (let c = 0; c < 4; c++) {
          const wx = -s * 0.3 + c * (s * 0.7 / 4);
          const wy = -s * 0.48 + r * (s * 1.0 / 8);
          // 跳过中央警告标志区域
          if (Math.abs(wx) < s * 0.18 && wy > -s * 0.22 && wy < s * 0.22) continue;
          ctx.fillStyle = (wMap && wMap[r] && wMap[r][c]) ? '#ff4040' : '#4a1010';
          ctx.fillRect(wx, wy, ww, wh);
        }
      }

      // 底部入口（黑色裂缝）
      ctx.fillStyle = '#1a0000';
      ctx.fillRect(-s * 0.1, s * 0.42, s * 0.2, s * 0.13);
      ctx.fillStyle = `rgba(255, 30, 30, ${0.4 + 0.3 * pulseAlpha})`;
      ctx.fillRect(-s * 0.06, s * 0.44, s * 0.12, s * 0.06);

      ctx.restore(); // 恢复脉冲缩放
      break;
    }

    case 'bridge':
      // 桥面
      ctx.fillStyle = '#546e7a';
      ctx.fillRect(-s * 0.5, -s * 0.05, s, s * 0.1);
      // 桥墩
      ctx.fillStyle = '#455a64';
      ctx.fillRect(-s * 0.4, -s * 0.05, s * 0.08, s * 0.35);
      ctx.fillRect(s * 0.32, -s * 0.05, s * 0.08, s * 0.35);
      // 拉索
      ctx.strokeStyle = '#78909c';
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.moveTo(-s * 0.35, -s * 0.3);
      ctx.lineTo(0, -s * 0.05);
      ctx.lineTo(s * 0.35, -s * 0.3);
      ctx.stroke();
      // 塔
      ctx.fillStyle = '#37474f';
      ctx.fillRect(-s * 0.38, -s * 0.35, s * 0.06, s * 0.3);
      ctx.fillRect(s * 0.32, -s * 0.35, s * 0.06, s * 0.3);
      break;

    // ─── 限时宝石：六角水晶 + 外发光 + 倒计时光环 ───
    case 'gem': {
      // 外层大范围柔光（脉冲效果）
      const pulseScale = 1 + 0.15 * Math.sin(Date.now() * 0.008);
      const outerGlow = ctx.createRadialGradient(0, 0, s * 0.2, 0, 0, s * 1.8 * pulseScale);
      outerGlow.addColorStop(0, 'rgba(224, 64, 251, 0.25)');
      outerGlow.addColorStop(0.5, 'rgba(156, 39, 176, 0.1)');
      outerGlow.addColorStop(1, 'rgba(156, 39, 176, 0)');
      ctx.fillStyle = outerGlow;
      ctx.beginPath();
      ctx.arc(0, 0, s * 1.8 * pulseScale, 0, Math.PI * 2);
      ctx.fill();

      // 倒计时光环（显示剩余时间比例）
      if (item.isLimited && item.timeLeft !== undefined) {
        const ratio = item.timeLeft / GEM_LIFETIME;
        ctx.strokeStyle = ratio > 0.4 ? '#e040fb' : '#ff1744';
        ctx.lineWidth = 3;
        ctx.beginPath();
        ctx.arc(0, 0, s * 0.9, -Math.PI / 2, -Math.PI / 2 + Math.PI * 2 * ratio);
        ctx.stroke();
      }

      // 水晶主体（六角形）
      ctx.fillStyle = '#e040fb';
      ctx.beginPath();
      ctx.moveTo(0, -s * 0.7);
      ctx.lineTo(s * 0.45, -s * 0.25);
      ctx.lineTo(s * 0.45, s * 0.25);
      ctx.lineTo(0, s * 0.7);
      ctx.lineTo(-s * 0.45, s * 0.25);
      ctx.lineTo(-s * 0.45, -s * 0.25);
      ctx.closePath();
      ctx.fill();

      // 水晶上半高光面
      ctx.fillStyle = '#ea80fc';
      ctx.beginPath();
      ctx.moveTo(0, -s * 0.7);
      ctx.lineTo(s * 0.45, -s * 0.25);
      ctx.lineTo(0, 0);
      ctx.lineTo(-s * 0.45, -s * 0.25);
      ctx.closePath();
      ctx.fill();

      // 中心亮点
      ctx.fillStyle = '#f3e5f5';
      ctx.beginPath();
      ctx.moveTo(0, -s * 0.35);
      ctx.lineTo(s * 0.18, 0);
      ctx.lineTo(0, s * 0.1);
      ctx.lineTo(-s * 0.18, 0);
      ctx.closePath();
      ctx.fill();

      // 顶部星芒闪烁
      const starAngle = Date.now() * 0.003;
      ctx.strokeStyle = 'rgba(255,255,255,0.6)';
      ctx.lineWidth = 1.5;
      for (let i = 0; i < 4; i++) {
        const a = starAngle + i * Math.PI / 2;
        ctx.beginPath();
        ctx.moveTo(Math.cos(a) * s * 0.15, -s * 0.7 + Math.sin(a) * s * 0.15);
        ctx.lineTo(Math.cos(a) * s * 0.3, -s * 0.7 + Math.sin(a) * s * 0.3);
        ctx.stroke();
      }
      break;
    }
  }

  ctx.restore();
}

/** 绘制黑洞 */
function drawBlackHole(dt) {
  const { x, y, radius } = blackHole;
  const gravRange = blackHole.getGravityRange();
  const isRainbow = score >= RAINBOW_SCORE;

  // 彩虹模式旋转速度翻倍（基于实际帧时间累加）
  let rotation;
  if (isRainbow) {
    blackHole.rotation += (0.02 + blackHole.radius * 0.0001);
    rotation = blackHole.rotation;
  } else {
    rotation = blackHole.rotation;
  }

  // --- 引力范围光圈（彩虹模式扩大范围） ---
  const glowRange = isRainbow ? gravRange * 1.35 : gravRange;
  if (isRainbow) {
    const stops = [];
    for (let i = 0; i <= 8; i++) {
      const t = i / 8;
      stops.push({ pos: t, color: rainbowColor(t * 360, 0.14 * (1 - t * t)) });
    }
    const gravGrad = ctx.createRadialGradient(x, y, radius, x, y, glowRange);
    for (const s of stops) gravGrad.addColorStop(s.pos, s.color);
    ctx.fillStyle = gravGrad;
  } else {
    const gravGrad = ctx.createRadialGradient(x, y, radius, x, y, glowRange);
    gravGrad.addColorStop(0, 'rgba(128, 0, 255, 0.12)');
    gravGrad.addColorStop(0.5, 'rgba(100, 50, 255, 0.05)');
    gravGrad.addColorStop(1, 'rgba(100, 50, 255, 0)');
    ctx.fillStyle = gravGrad;
  }
  ctx.beginPath();
  ctx.arc(x, y, glowRange, 0, Math.PI * 2);
  ctx.fill();

  // --- 旋转光晕（外层吸积盘） ---
  ctx.save();
  ctx.translate(x, y);
  ctx.rotate(rotation);
  if (isRainbow) {
    const diskGrad = ctx.createRadialGradient(0, 0, radius * 0.6, 0, 0, radius * 2.2);
    diskGrad.addColorStop(0,    rainbowColor(0, 0));
    diskGrad.addColorStop(0.2,  rainbowColor(60,  0.35));
    diskGrad.addColorStop(0.4,  rainbowColor(120, 0.45));
    diskGrad.addColorStop(0.6,  rainbowColor(180, 0.35));
    diskGrad.addColorStop(0.8,  rainbowColor(240, 0.2));
    diskGrad.addColorStop(1,    rainbowColor(300, 0));
    ctx.fillStyle = diskGrad;
  } else {
    const diskGrad = ctx.createRadialGradient(0, 0, radius * 0.6, 0, 0, radius * 1.8);
    diskGrad.addColorStop(0, 'rgba(180, 80, 255, 0)');
    diskGrad.addColorStop(0.3, 'rgba(140, 50, 255, 0.35)');
    diskGrad.addColorStop(0.6, 'rgba(80, 30, 200, 0.2)');
    diskGrad.addColorStop(1, 'rgba(60, 20, 180, 0)');
    ctx.fillStyle = diskGrad;
  }
  ctx.scale(1, 0.5);
  ctx.beginPath();
  ctx.arc(0, 0, isRainbow ? radius * 2.2 : radius * 1.8, 0, Math.PI * 2);
  ctx.fill();
  ctx.restore();

  // --- 第二层旋转光环 ---
  ctx.save();
  ctx.translate(x, y);
  ctx.rotate(-rotation * 1.5);
  if (isRainbow) {
    const ringGrad = ctx.createRadialGradient(0, 0, radius * 0.9, 0, 0, radius * 1.6);
    ringGrad.addColorStop(0,   rainbowColor(180, 0));
    ringGrad.addColorStop(0.3, rainbowColor(220, 0.4));
    ringGrad.addColorStop(0.6, rainbowColor(280, 0.5));
    ringGrad.addColorStop(1,   rainbowColor(340, 0));
    ctx.fillStyle = ringGrad;
    ctx.beginPath();
    ctx.arc(0, 0, radius * 1.6, 0, Math.PI * 2);
    ctx.fill();
  } else {
    const ringGrad = ctx.createRadialGradient(0, 0, radius * 0.9, 0, 0, radius * 1.3);
    ringGrad.addColorStop(0, 'rgba(100, 100, 255, 0)');
    ringGrad.addColorStop(0.5, 'rgba(150, 80, 255, 0.4)');
    ringGrad.addColorStop(1, 'rgba(100, 50, 255, 0)');
    ctx.fillStyle = ringGrad;
    ctx.beginPath();
    ctx.arc(0, 0, radius * 1.3, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.restore();

  // --- 彩虹模式：额外嵌套彩色光环层 ---
  if (isRainbow) {
    const ringLayers = [
      { speed: 2.0, scale: 1.0, radiusMul: 1.85, width: 4, alpha: 0.55 },
      { speed: -1.3, scale: 0.5, radiusMul: 1.55, width: 6, alpha: 0.45 },
      { speed: 0.7, scale: 1.5, radiusMul: 2.05, width: 3, alpha: 0.35 },
    ];
    for (const layer of ringLayers) {
      ctx.save();
      ctx.translate(x, y);
      ctx.rotate(rotation * layer.speed);
      ctx.scale(1, layer.scale);
      ctx.lineWidth = layer.width;
      for (let i = 0; i < 36; i++) {
        const a0 = (i / 36) * Math.PI * 2;
        const a1 = ((i + 1) / 36) * Math.PI * 2;
        ctx.strokeStyle = rainbowColor(i * 10, layer.alpha);
        ctx.beginPath();
        ctx.arc(0, 0, radius * layer.radiusMul, a0, a1);
        ctx.stroke();
      }
      ctx.restore();
    }
  }

  // --- 黑洞核心（纯黑 + 发光边缘） ---
  const edgeGrad = ctx.createRadialGradient(x, y, radius * 0.7, x, y, radius * 1.1);
  if (isRainbow) {
    edgeGrad.addColorStop(0, 'rgba(0, 0, 0, 1)');
    edgeGrad.addColorStop(0.65, rainbowColor(0, 0.7));
    edgeGrad.addColorStop(0.85, rainbowColor(120, 0.45));
    edgeGrad.addColorStop(1, rainbowColor(240, 0));
  } else {
    edgeGrad.addColorStop(0, 'rgba(0, 0, 0, 1)');
    edgeGrad.addColorStop(0.7, 'rgba(80, 20, 180, 0.6)');
    edgeGrad.addColorStop(1, 'rgba(120, 50, 255, 0)');
  }
  ctx.fillStyle = edgeGrad;
  ctx.beginPath();
  ctx.arc(x, y, radius * 1.1, 0, Math.PI * 2);
  ctx.fill();

  // 纯黑核心
  ctx.fillStyle = '#000';
  ctx.beginPath();
  ctx.arc(x, y, radius, 0, Math.PI * 2);
  ctx.fill();
}

/** 绘制粒子 */
function drawParticles() {
  for (const p of particles) {
    ctx.globalAlpha = p.life;
    ctx.fillStyle = p.color;
    ctx.beginPath();
    ctx.arc(p.x, p.y, p.size * p.life, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.globalAlpha = 1;
}

/** 绘制被吸附物品的引力尾迹 */
function drawAttractTrails() {
  for (const item of items) {
    if (!item.attracted) continue;
    const speed = Math.sqrt(item.vx * item.vx + item.vy * item.vy);
    if (speed < 0.5) continue;
    // 拖尾方向与速度相反
    const trailLen = Math.min(speed * 5, 30);
    const angle = Math.atan2(item.vy, item.vx);
    const grad = ctx.createLinearGradient(
      item.x, item.y,
      item.x - Math.cos(angle) * trailLen,
      item.y - Math.sin(angle) * trailLen
    );
    grad.addColorStop(0, item.color + '80');
    grad.addColorStop(1, item.color + '00');
    ctx.strokeStyle = grad;
    ctx.lineWidth = item.size * 0.3;
    ctx.lineCap = 'round';
    ctx.beginPath();
    ctx.moveTo(item.x, item.y);
    ctx.lineTo(
      item.x - Math.cos(angle) * trailLen,
      item.y - Math.sin(angle) * trailLen
    );
    ctx.stroke();
  }
}

// ===================== 工具函数 =====================

/** 圆角矩形 */
function roundRect(x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.lineTo(x + w - r, y);
  ctx.quadraticCurveTo(x + w, y, x + w, y + r);
  ctx.lineTo(x + w, y + h - r);
  ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
  ctx.lineTo(x + r, y + h);
  ctx.quadraticCurveTo(x, y + h, x, y + h - r);
  ctx.lineTo(x, y + r);
  ctx.quadraticCurveTo(x, y, x + r, y);
  ctx.fill();
}

/** 颜色加深/变亮 */
function shadeColor(hex, percent) {
  const num = parseInt(hex.slice(1), 16);
  const r = Math.min(255, Math.max(0, (num >> 16) + percent));
  const g = Math.min(255, Math.max(0, ((num >> 8) & 0x00FF) + percent));
  const b = Math.min(255, Math.max(0, (num & 0x0000FF) + percent));
  return `rgb(${r},${g},${b})`;
}

// ===================== 背景变暗效果 =====================
function drawDarkOverlay() {
  const isRainbow = score >= RAINBOW_SCORE;
  if (blackHole.radius < STAR_THRESHOLD && !isRainbow) return;
  const baseAlpha = isRainbow
    ? Math.max(0.4, Math.min(0.55, (blackHole.radius - STAR_THRESHOLD) / 200))
    : Math.min(0.5, (blackHole.radius - STAR_THRESHOLD) / 200);
  ctx.fillStyle = `rgba(0,0,0,${baseAlpha})`;
  ctx.fillRect(0, 0, WORLD_W, WORLD_H);
}

// ===================== 世界边界绘制 =====================
function drawWorldBorder() {
  ctx.strokeStyle = '#ff4444';
  ctx.lineWidth = 4;
  ctx.setLineDash([15, 10]);
  ctx.strokeRect(2, 2, WORLD_W - 4, WORLD_H - 4);
  ctx.setLineDash([]);
}

// ===================== HUD 更新 =====================
function updateHUD() {
  hudScore.textContent = score;
  hudRadius.textContent = Math.round(blackHole.radius);

  // 胜利后不再更新倒计时显示
  if (gameState === 'over' && timeLeft > 0) {
    // 胜利结局：显示胜利字样
    hudTimer.textContent = '胜利!';
    hudTimer.classList.remove('time-warning');
  } else {
    hudTimer.textContent = Math.ceil(timeLeft);
    // 时间不足30秒（加速阶段）时变红
    if (timeLeft <= HURRY_UP_TIME) {
      hudTimer.classList.add('time-warning');
    } else {
      hudTimer.classList.remove('time-warning');
    }
  }
}

// ===================== 主游戏循环 =====================
function gameLoop(timestamp) {
  if (gameState !== 'playing') return;

  // 计算 delta time
  if (!lastTime) lastTime = timestamp;
  const dt = (timestamp - lastTime) / 1000;
  lastTime = timestamp;

  // 倒计时（最后30秒加速）
  const timeFactor = timeLeft <= HURRY_UP_TIME ? HURRY_UP_FACTOR : 1;
  timerAcc += dt * timeFactor;
  if (timerAcc >= 1) {
    timeLeft -= Math.floor(timerAcc);
    timerAcc %= 1;
    if (timeLeft <= 0) {
      timeLeft = 0;
      endGame(false); // 时间耗尽 → 失败
      return;
    }
  }

  // 限时宝石生成
  const elapsed = GAME_DURATION - timeLeft;
  if (elapsed >= GEM_FIRST_DELAY) {
    gemSpawnAcc += dt;
    if (gemSpawnAcc >= GEM_SPAWN_INTERVAL) {
      gemSpawnAcc -= GEM_SPAWN_INTERVAL;
      spawnGem();
    }
  }

  // 边缘建筑消失（游戏过半后激活）
  updateEdgeRemoval(dt);

  // 更新逻辑
  blackHole.update(dt);
  updateItems(dt);
  updateParticles();
  camera.update();

  // ===== 渲染 =====
  ctx.clearRect(0, 0, canvas.width, canvas.height);

  // 应用相机变换（含震动）
  ctx.save();
  ctx.translate(-camera.x + camera.shakeX, -camera.y + camera.shakeY);

  // 分层绘制
  drawGround();
  drawStars();
  drawDarkOverlay();
  drawWorldBorder();

  // 按大小排序物品（小的先画，大的后画，形成遮挡）
  const sortedItems = [...items].sort((a, b) => a.size - b.size);

  // 绘制物品（比黑洞小的先画，比黑洞大的后画）
  for (const item of sortedItems) {
    if (item.size <= blackHole.radius) {
      drawItem(item);
    }
  }

  // 绘制引力尾迹
  drawAttractTrails();

  // 绘制黑洞
  drawBlackHole(dt);

  // 绘制比黑洞大的物品（遮挡黑洞）
  for (const item of sortedItems) {
    if (item.size > blackHole.radius) {
      drawItem(item);
    }
  }

  // 绘制粒子（最顶层）
  drawParticles();

  ctx.restore();

  // 更新 HUD
  updateHUD();

  // 下一帧
  requestAnimationFrame(gameLoop);
}

// ===================== 游戏控制 =====================

/** 开始/重新开始游戏 */
function startGame() {
  // 重置状态
  score = 0;
  timeLeft = GAME_DURATION;
  absorbCount = 0;
  timerAcc = 0;
  lastTime = 0;
  particles = [];
  absorbedTypes = new Set(); // ★ 重置已吞噬类型记录
  gemSpawnAcc = 0;
  edgeRemovalAcc = 0;
  edgeRemovalActive = false;
  speedDebuffTimer = 0;

  // 重置黑洞
  blackHole.x = WORLD_W / 2;
  blackHole.y = WORLD_H / 2;
  blackHole.radius = 20;
  blackHole.speed = BASE_SPEED;
  blackHole.rotation = 0;
  blackHole.vx = 0;
  blackHole.vy = 0;

  // 重置相机
  camera.x = blackHole.x - canvas.width / 2;
  camera.y = blackHole.y - canvas.height / 2;
  camera.shakeIntensity = 0;

  // ★ 预计算街区矩形（路网渲染用）
  blockRects = computeBlockRects();

  // 生成城市
  populateCity();
  initStars();

  // 切换状态
  gameState = 'playing';
  startScr.classList.add('hidden');
  endScr.classList.add('hidden');

  // 重置结束面板样式（移除上一次可能留下的胜利样式）
  const endTitle = document.getElementById('end-title');
  const endMsg   = document.getElementById('end-message');
  if (endTitle) {
    endTitle.textContent = '游戏结束';
    endTitle.style.color = '';
  }
  if (endMsg) endMsg.textContent = '';

  // 启动游戏循环
  requestAnimationFrame(gameLoop);
}

/** 结束游戏
 *  @param {boolean} isWin - true 表示胜利结局，false 表示时间耗尽失败
 */
function endGame(isWin = false) {
  gameState = 'over';

  // 填充结算数据
  document.getElementById('final-score').textContent  = score;
  document.getElementById('final-radius').textContent = Math.round(blackHole.radius);
  document.getElementById('final-count').textContent  = absorbCount;

  // ★ 根据胜败显示不同标题与提示（兼容 HTML 中可能没有这些元素的情况）
  const endTitle = document.getElementById('end-title');
  const endMsg   = document.getElementById('end-message');

  if (isWin) {
    if (endTitle) {
      endTitle.textContent = '🎉 胜利!';
      endTitle.style.color = '#ffd700';
    }
    if (endMsg) {
      const remaining = Math.ceil(timeLeft);
      endMsg.textContent = `城市已被完全吞噬!剩余时间 ${remaining} 秒`;
    }
    // 强制更新 HUD 显示胜利字样
    updateHUD();
  } else {
    if (endTitle) {
      endTitle.textContent = '时间到!';
      endTitle.style.color = '#ff4444';
    }
    if (endMsg) {
      const collected = absorbedTypes.size;
      endMsg.textContent = `已收集 ${collected}/${TOTAL_TYPE_COUNT} 种物品,继续努力!`;
    }
  }

  endScr.classList.remove('hidden');
}

// ===================== 事件绑定 =====================
startBtn.addEventListener('click', startGame);
restartBtn.addEventListener('click', startGame);
