console.log("app.js loaded successfully (New Compression Version)");

// LOCAL LZW COMPRESSION ENGINE
function lzwCompress(str) {
  var dictionary = {};
  var phrase = "";
  var code = 256;
  var output = [];
  var utfStr = unescape(encodeURIComponent(str));
  for (var i = 0; i < utfStr.length; i++) {
    var char = utfStr.charAt(i);
    if (dictionary[phrase + char] !== undefined) {
      phrase += char;
    } else {
      output.push(
        phrase.length > 1 ? dictionary[phrase] : phrase.charCodeAt(0),
      );
      dictionary[phrase + char] = code++;
      phrase = char;
    }
  }
  if (phrase !== "") {
    output.push(phrase.length > 1 ? dictionary[phrase] : phrase.charCodeAt(0));
  }
  return String.fromCharCode.apply(null, output);
}

function lzwDecompress(str) {
  var dictionary = {};
  var currChar = str.charAt(0);
  var oldPhrase = currChar;
  var output = [currChar];
  var code = 256;
  for (var i = 1; i < str.length; i++) {
    var currCode = str.charCodeAt(i);
    var phrase;
    if (currCode < 256) {
      phrase = str.charAt(i);
    } else {
      phrase = dictionary[currCode]
        ? dictionary[currCode]
        : oldPhrase + currChar;
    }
    output.push(phrase);
    currChar = phrase.charAt(0);
    dictionary[code++] = oldPhrase + currChar;
    oldPhrase = phrase;
  }
  return decodeURIComponent(escape(output.join("")));
}

function encodeString(str) {
  try {
    let compressed = lzwCompress(str);
    return btoa(compressed);
  } catch (e) {
    return btoa(unescape(encodeURIComponent(str)));
  }
}

function decodeString(str) {
  try {
    let raw = atob(str);
    return lzwDecompress(raw);
  } catch (e) {
    try {
      return decodeURIComponent(escape(atob(str)));
    } catch (e2) {
      const numDecodeMap = {
        ")": "0",
        "!": "1",
        "@": "2",
        "#": "3",
        $: "4",
        "%": "5",
        "^": "6",
        "&": "7",
        "*": "8",
        "(": "9",
      };
      return str
        .split("")
        .map((char) => {
          if (char >= "a" && char <= "z")
            return String.fromCharCode(
              ((char.charCodeAt(0) - 97 - 1 + 26) % 26) + 97,
            );
          if (char >= "A" && char <= "Z")
            return String.fromCharCode(
              ((char.charCodeAt(0) - 65 - 1 + 26) % 26) + 65,
            );
          if (numDecodeMap[char]) return numDecodeMap[char];
          return char;
        })
        .join("");
    }
  }
}

// --- SOLUTION PARSING & FORMATTING ---
function parseSolutionString(solStr) {
  let paths = [];
  let explanation = "";
  if (!solStr) return { paths, explanation };
  let parts = solStr.split(";");
  let movesPart = parts[0].trim();
  explanation = parts.slice(1).join(";").trim();

  let regex = /\(([^)]+)\)/g;
  let match;
  let foundBlocks = false;
  while ((match = regex.exec(movesPart)) !== null) {
    foundBlocks = true;
    let moves = match[1]
      .split(/[, ]+/)
      .map((m) => m.trim())
      .filter((m) => m.length >= 4);
    if (moves.length > 0) paths.push(moves);
  }
  if (!foundBlocks && movesPart.length > 0) {
    let moves = movesPart
      .split(/[, ]+/)
      .map((m) => m.trim())
      .filter((m) => m.length >= 4);
    if (moves.length > 0) paths.push(moves);
  }
  return { paths, explanation };
}

function formatSolutionString(paths, explanation) {
  let solStr = paths.map((p) => `(${p.join(",")})`).join(",");
  if (explanation) solStr += `;${explanation}`;
  return solStr;
}

// 1. CONSTANTS AND MAPS
const pieceSVGs = {
  p: "images/Chess_pdt45.svg",
  n: "images/Chess_ndt45.svg",
  b: "images/Chess_bdt45.svg",
  r: "images/Chess_rdt45.svg",
  q: "images/Chess_qdt45.svg",
  k: "images/Chess_kdt45.svg",
  P: "images/Chess_plt45.svg",
  N: "images/Chess_nlt45.svg",
  B: "images/Chess_blt45.svg",
  R: "images/Chess_rlt45.svg",
  Q: "images/Chess_qlt45.svg",
  K: "images/Chess_klt45.svg",
};

const sounds = {
  move: new Audio("sounds/move-self.mp3"),
  capture: new Audio("sounds/capture.mp3"),
  check: new Audio("sounds/move-check.mp3"),
  castle: new Audio("sounds/castle.mp3"),
  promote: new Audio("sounds/promote.mp3"),
  notify: new Audio("sounds/notify.mp3"),
};

// 2. STATE VARIABLES
let chess = new Chess();
let currentView = "view-home";
let makerBoardFlipped = false;
let solverBoardFlipped = false;
let activePuzzle = null;
let selectedSquare = null;
let hintCount = 3;
let originalHintCount = 0;
let isBotThinking = false;
let isMakerPreviewing = false;
let isMuted = false;

let solutionPaths = [];
let currentPathIndex = -1;
let currentMoveIndex = 0;
let puzzleExplanation = "";
let previewInitialPaths = [];
let previewActivePathIndex = -1;

let dragState = {
  isDragging: false,
  potentialDrag: false,
  justDragged: false,
  source: null,
  boardId: null,
  piece: null,
  startSquare: null,
  startX: 0,
  startY: 0,
  ghostEl: null,
  bgImage: "",
};

const boardArrows = { "maker-board": [], "solver-board": [] };
let originalSolverFen = "";
let originalMovesRequired = 0;

// 3. STOCKFISH INITIALIZATION (Using Blob URL to bypass CORS)
let stockfish = null;
let engineQueue = [];
let isEngineCalculating = false;
let currentMultiPvMoves = [];

if (window.location.protocol !== "file:") {
  const stockfishCdnUrl =
    "https://cdn.jsdelivr.net/npm/stockfish.js@10.0.2/stockfish.js";

  fetch(stockfishCdnUrl)
    .then((response) => response.text())
    .then((scriptContent) => {
      const blob = new Blob([scriptContent], {
        type: "application/javascript",
      });
      const blobUrl = URL.createObjectURL(blob);

      stockfish = new Worker(blobUrl);
      URL.revokeObjectURL(blobUrl);

      stockfish.onmessage = function (event) {
        const line = event.data;
        if (typeof line !== "string") return;

        if (line.includes("info depth") && line.includes("multipv")) {
          let pvMatch = line.match(/ pv (\w{4,5})/);
          if (pvMatch) {
            let multipvMatch = line.match(/multipv (\d+)/);
            let index = multipvMatch ? parseInt(multipvMatch[1]) - 1 : 0;
            currentMultiPvMoves[index] = pvMatch[1];
          }
        }

        if (line.includes("info depth") && line.includes("score")) {
          let cpMatch = line.match(/score cp (-?\d+)/);
          let mateMatch = line.match(/score mate (-?\d+)/);
          let turn = chess.turn();
          if (cpMatch) updateEvalUI(parseInt(cpMatch[1]), turn);
          else if (mateMatch) updateEvalMate(parseInt(mateMatch[1]), turn);
        }

        if (line.includes("bestmove")) {
          isEngineCalculating = false;
          let bm = line.split(" ")[1];
          if (bm && bm !== "(none)") currentMultiPvMoves[0] = bm;
          if (engineQueue.length > 0) {
            let req = engineQueue.shift();
            if (req.resolve) req.resolve(currentMultiPvMoves);
          }
          currentMultiPvMoves = [];
          processEngineQueue();
        }
      };
      console.log("Stockfish loaded successfully via Blob URL.");
    })
    .catch((error) => {
      console.warn("Stockfish failed to load via Blob URL.", error);
      stockfish = null;
    });
} else {
  console.log("Running via file:// - Stockfish engine disabled for stability.");
}

function getEngineMoves(fen, multipv = 1, timeoutMs = 4000) {
  return new Promise((resolve) => {
    if (!stockfish) {
      resolve([]);
      return;
    }
    let timeout = setTimeout(() => {
      engineQueue = engineQueue.filter((q) => q.resolve !== resolve);
      if (engineQueue.length === 0) isEngineCalculating = false;
      processEngineQueue();
      resolve([]);
    }, timeoutMs);

    engineQueue.push({
      resolve: (moves) => {
        clearTimeout(timeout);
        resolve(moves);
      },
      fen,
      multipv,
      depth: 12,
    });
    processEngineQueue();
  });
}

function evaluatePosition(fen, movetime = 0) {
  if (!stockfish || (!activePuzzle && !isMakerPreviewing)) return;
  if (chess.game_over()) {
    if (chess.in_checkmate())
      applyEvalBar(
        chess.turn() === "w" ? 0 : 100,
        chess.turn() === "w" ? "0-1" : "1-0",
      );
    else applyEvalBar(50, "0.5");
    return;
  }
  engineQueue = engineQueue.filter((q) => q.resolve !== null);
  engineQueue.push({
    resolve: null,
    fen: fen,
    multipv: 1,
    depth: movetime ? null : 12,
    movetime: movetime > 0 ? movetime : null,
  });
  processEngineQueue();
}

function processEngineQueue() {
  if (!stockfish || isEngineCalculating || engineQueue.length === 0) return;
  isEngineCalculating = true;
  currentMultiPvMoves = [];
  let req = engineQueue[0];
  stockfish.postMessage(`setoption name MultiPV value ${req.multipv || 1}`);
  stockfish.postMessage(`position fen ${req.fen}`);
  if (req.movetime) stockfish.postMessage(`go movetime ${req.movetime}`);
  else stockfish.postMessage(`go depth ${req.depth || 12}`);
}

// 4. CORE FUNCTIONS
function toggleMute() {
  isMuted = !isMuted;
  const iconSrc = isMuted ? "images/speaker-mute.svg" : "images/speaker-on.svg";
  document.querySelectorAll(".mute-icon").forEach((img) => {
    img.src = iconSrc;
  });
}

function playSound(move) {
  if (!move || isMuted) return;
  if (move.san.includes("+") || move.san.includes("#"))
    sounds.check.play().catch((e) => {});
  else if (move.flags.includes("c") || move.flags.includes("e"))
    sounds.capture.play().catch((e) => {});
  else if (move.flags.includes("k") || move.flags.includes("q"))
    sounds.castle.play().catch((e) => {});
  else if (move.flags.includes("p")) sounds.promote.play().catch((e) => {});
  else sounds.move.play().catch((e) => {});
}

function updateEvalUI(cp, turn) {
  if (turn === "b") cp = -cp;
  let percentage = Math.max(5, Math.min(95, 50 + (cp / 100) * 3));
  applyEvalBar(percentage, (cp / 100).toFixed(1));
}

function updateEvalMate(mate, turn) {
  if (turn === "b") mate = -mate;
  applyEvalBar(mate > 0 ? 100 : 0, `M${Math.abs(mate)}`);
}

function applyEvalBar(percentage, text) {
  let prefix = currentView === "view-solver" ? "solver" : "maker";
  const w = document.getElementById(prefix + "-eval-white");
  const b = document.getElementById(prefix + "-eval-black");
  const s = document.getElementById(prefix + "-eval-score");
  if (w && b) {
    w.style.height = percentage + "%";
    b.style.height = 100 - percentage + "%";
  }
  if (s) s.innerText = text;
}

function nav(viewId) {
  document
    .querySelectorAll(".view")
    .forEach((v) => v.classList.remove("active"));
  document.getElementById(viewId).classList.add("active");
  currentView = viewId;
  if (viewId === "view-list") renderPuzzleList();
}

function parseCustomFEN(fen) {
  let parts = fen.split(" ");
  let flip = false;
  if (parts.length > 6) {
    let last = parts.pop().toUpperCase();
    if (last === "B") flip = true;
  }
  return { standardFen: parts.join(" "), flip: flip };
}

function renderBoard(containerId, fen, flipped, lastMove = null) {
  const container = document.getElementById(containerId);
  if (!container) return;
  container.innerHTML = "";
  const svg = document.getElementById(containerId + "-svg");
  if (svg) svg.innerHTML = "";
  boardArrows[containerId] = [];

  chess.load(fen);
  const board = chess.board();
  let ranks = [8, 7, 6, 5, 4, 3, 2, 1];
  let files = ["a", "b", "c", "d", "e", "f", "g", "h"];
  if (flipped) {
    ranks.reverse();
    files.reverse();
  }

  ranks.forEach((rank, rowIndex) => {
    files.forEach((file, colIndex) => {
      const square = document.createElement("div");
      let isDark = (rowIndex + colIndex) % 2 === 0;
      if (flipped) isDark = !isDark;
      square.className = `square ${isDark ? "dark" : "light"}`;
      square.dataset.square = file + rank;

      if (
        lastMove &&
        (square.dataset.square === lastMove.from ||
          square.dataset.square === lastMove.to)
      )
        square.classList.add("highlight-last");
      if (colIndex === 0) {
        const r = document.createElement("span");
        r.className = "coord-rank";
        r.innerText = rank;
        square.appendChild(r);
      }
      if (rowIndex === 7) {
        const f = document.createElement("span");
        f.className = "coord-file";
        f.innerText = file;
        square.appendChild(f);
      }

      const piece = board[8 - rank][file.charCodeAt(0) - 97];
      if (piece) {
        const pieceDiv = document.createElement("div");
        pieceDiv.className = "piece";
        pieceDiv.style.backgroundImage = `url(${pieceSVGs[piece.color === "w" ? piece.type.toUpperCase() : piece.type]})`;
        square.appendChild(pieceDiv);
      }
      container.appendChild(square);
    });
  });
}

function showExplanationIfAny(puzzle) {
  if (!puzzle || !puzzle.solution) return;
  let parts = puzzle.solution.split(";");
  let explanation = parts.slice(1).join(";").trim();
  if (explanation) {
    document.getElementById("explanation-box").value = explanation;
    document.getElementById("explanation-box").classList.remove("hidden");
  }
}

function playPreMoves(movesStr, boardId, flipped, onComplete) {
  if (!movesStr || movesStr.trim() === "") {
    onComplete();
    return;
  }
  let moves = movesStr
    .split(",")
    .map((m) => m.trim())
    .filter((m) => m.length >= 4);
  if (moves.length === 0) {
    onComplete();
    return;
  }
  let i = 0;
  function step() {
    if (i >= moves.length) {
      onComplete();
      return;
    }
    let m = moves[i];
    try {
      let move = chess.move({
        from: m.substring(0, 2),
        to: m.substring(2, 4),
        promotion: "q",
      });
      if (move) {
        playSound(move);
        renderBoard(boardId, chess.fen(), flipped, move);
        evaluatePosition(chess.fen());
      }
    } catch (e) {
      console.error("Pre-move failed", m, e);
    }
    i++;
    setTimeout(step, 600);
  }
  step();
}

// DRAG AND DROP
function initPalette() {
  const palette = document.getElementById("piece-palette");
  if (!palette) return;
  palette.innerHTML = "";
  const pieces = ["p", "n", "b", "r", "q", "k"];
  pieces.forEach((p) => {
    let div = document.createElement("div");
    div.className = "palette-piece";
    div.dataset.piece = p;
    div.style.backgroundImage = `url(${pieceSVGs[p]})`;
    palette.appendChild(div);
  });
  pieces.forEach((p) => {
    let div = document.createElement("div");
    div.className = "palette-piece";
    div.dataset.piece = p.toUpperCase();
    div.style.backgroundImage = `url(${pieceSVGs[p.toUpperCase()]})`;
    palette.appendChild(div);
  });
}

function getBoardGrid() {
  let rows = chess.fen().split(" ")[0].split("/");
  return rows.map((row) => {
    let arr = [];
    for (let char of row) {
      if (isNaN(char)) arr.push(char);
      else for (let i = 0; i < parseInt(char); i++) arr.push("");
    }
    return arr;
  });
}

function saveBoardGrid(grid) {
  let newFenBoard = grid
    .map((row) => {
      let str = "",
        empty = 0;
      for (let char of row) {
        if (char === "") empty++;
        else {
          if (empty > 0) {
            str += empty;
            empty = 0;
          }
          str += char;
        }
      }
      if (empty > 0) str += empty;
      return str;
    })
    .join("/");

  let parts = chess.fen().split(" ");
  parts[0] = newFenBoard;
  let newFen = parts.join(" ");

  let flipStr = makerBoardFlipped ? " B" : " W";
  document.getElementById("fen-input").value = newFen + flipStr;

  chess.load(newFen);
  renderBoard("maker-board", newFen, makerBoardFlipped);
  evaluatePosition(newFen);
}

function handleDragStart(e) {
  dragState.isDragging = true;
  let ghost = document.createElement("div");
  ghost.className = "dragging-ghost";
  ghost.style.backgroundImage = dragState.bgImage;
  ghost.style.left = e.clientX + "px";
  ghost.style.top = e.clientY + "px";
  document.body.appendChild(ghost);
  dragState.ghostEl = ghost;
  if (dragState.source === "board") {
    const origPiece = document.querySelector(
      `#${dragState.boardId} [data-square="${dragState.startSquare}"] .piece`,
    );
    if (origPiece) origPiece.style.visibility = "hidden";
  }
}

function handleDragMove(e) {
  if (!dragState.isDragging && dragState.potentialDrag) {
    let dx = e.clientX - dragState.startX,
      dy = e.clientY - dragState.startY;
    if (Math.sqrt(dx * dx + dy * dy) > 5) {
      handleDragStart(e);
      dragState.potentialDrag = false;
    }
  }
  if (dragState.isDragging && dragState.ghostEl) {
    dragState.ghostEl.style.left = e.clientX + "px";
    dragState.ghostEl.style.top = e.clientY + "px";
  }
}

function handleDragEnd(e) {
  dragState.potentialDrag = false;
  if (!dragState.isDragging) return;
  if (dragState.ghostEl) {
    dragState.ghostEl.remove();
    dragState.ghostEl = null;
  }
  if (dragState.source === "board") {
    const origPiece = document.querySelector(
      `#${dragState.boardId} [data-square="${dragState.startSquare}"] .piece`,
    );
    if (origPiece) origPiece.style.visibility = "visible";
  }

  const dropTarget = document.elementFromPoint(e.clientX, e.clientY);
  let droppedOnBoard = false;
  if (dropTarget) {
    const squareEl = dropTarget.closest(".square");
    const targetBoardId = squareEl?.closest(".chessboard")?.id;
    if (squareEl && targetBoardId === dragState.boardId) {
      droppedOnBoard = true;
      let targetSquare = squareEl.dataset.square;
      if (dragState.boardId === "maker-board") {
        let grid = getBoardGrid();
        let tr = 8 - parseInt(targetSquare[1]),
          tc = targetSquare.charCodeAt(0) - 97;
        if (dragState.source === "board") {
          let sr = 8 - parseInt(dragState.startSquare[1]),
            sc = dragState.startSquare.charCodeAt(0) - 97;
          grid[sr][sc] = "";
        }
        grid[tr][tc] = dragState.piece;
        saveBoardGrid(grid);
      } else if (
        dragState.boardId === "solver-board" &&
        dragState.source === "board"
      ) {
        attemptMove(dragState.startSquare, targetSquare, "solver-board");
      }
    }
  }
  if (
    !droppedOnBoard &&
    dragState.source === "board" &&
    dragState.boardId === "maker-board"
  ) {
    let grid = getBoardGrid();
    let sr = 8 - parseInt(dragState.startSquare[1]),
      sc = dragState.startSquare.charCodeAt(0) - 97;
    grid[sr][sc] = "";
    saveBoardGrid(grid);
  }
  dragState.isDragging = false;
  dragState.justDragged = true;
  setTimeout(() => {
    dragState.justDragged = false;
  }, 100);
}

function setupDragging() {
  const palette = document.getElementById("piece-palette");
  if (palette) {
    palette.addEventListener("mousedown", (e) => {
      e.preventDefault();
      const target = e.target.closest(".palette-piece");
      if (target) {
        dragState.potentialDrag = true;
        dragState.source = "palette";
        dragState.boardId = "maker-board";
        dragState.piece = target.dataset.piece;
        dragState.startSquare = null;
        dragState.bgImage = target.style.backgroundImage;
        dragState.startX = e.clientX;
        dragState.startY = e.clientY;
      }
    });
  }
  const makerBoard = document.getElementById("maker-board");
  if (makerBoard) {
    makerBoard.addEventListener("mousedown", (e) => {
      if (isMakerPreviewing || e.button !== 0) return;
      const square = e.target.closest(".square");
      if (square && e.target.classList.contains("piece")) {
        e.preventDefault();
        let piece = chess.get(square.dataset.square);
        if (piece) {
          dragState.potentialDrag = true;
          dragState.source = "board";
          dragState.boardId = "maker-board";
          dragState.piece =
            piece.color === "w" ? piece.type.toUpperCase() : piece.type;
          dragState.startSquare = square.dataset.square;
          dragState.bgImage = e.target.style.backgroundImage;
          dragState.startX = e.clientX;
          dragState.startY = e.clientY;
        }
      }
    });
  }
  const solverBoard = document.getElementById("solver-board");
  if (solverBoard) {
    solverBoard.addEventListener("mousedown", (e) => {
      if (e.button !== 0 || isBotThinking) return;
      const square = e.target.closest(".square");
      if (square && e.target.classList.contains("piece")) {
        e.preventDefault();
        let piece = chess.get(square.dataset.square);
        if (piece && piece.color === chess.turn()) {
          dragState.potentialDrag = true;
          dragState.source = "board";
          dragState.boardId = "solver-board";
          dragState.piece =
            piece.color === "w" ? piece.type.toUpperCase() : piece.type;
          dragState.startSquare = square.dataset.square;
          dragState.bgImage = e.target.style.backgroundImage;
          dragState.startX = e.clientX;
          dragState.startY = e.clientY;
        }
      }
    });
  }
  window.addEventListener("mousemove", handleDragMove);
  window.addEventListener("mouseup", handleDragEnd);
}

// ARROWS LOGIC
function setupArrows(boardId, getFlipped) {
  const board = document.getElementById(boardId);
  if (!board) return;
  let startSquare = null,
    lastRightClickTime = 0;

  board.addEventListener("contextmenu", (e) => {
    e.preventDefault();
    e.stopPropagation();
  });
  board.addEventListener("mousedown", (e) => {
    if (e.button === 2) {
      e.preventDefault();
      let now = Date.now();
      if (now - lastRightClickTime < 300) {
        const svg = document.getElementById(boardId + "-svg");
        if (svg) svg.innerHTML = "";
        boardArrows[boardId] = [];
        startSquare = null;
        return;
      }
      lastRightClickTime = now;
      const square = e.target.closest(".square");
      if (square) {
        startSquare = square.dataset.square;
        const svg = document.getElementById(boardId + "-svg");
        if (svg)
          svg.querySelectorAll(".temp-arrow").forEach((el) => el.remove());
      }
    }
  });
  board.addEventListener("mousemove", (e) => {
    if (startSquare && e.buttons === 2) {
      const square = e.target.closest(".square");
      if (square && square.dataset.square !== startSquare)
        drawArrow(
          boardId,
          startSquare,
          square.dataset.square,
          getFlipped(),
          true,
        );
    }
  });
  board.addEventListener("mouseup", (e) => {
    if (e.button === 2 && startSquare) {
      e.preventDefault();
      const square = e.target.closest(".square");
      if (square && square.dataset.square !== startSquare) {
        let existingIndex = boardArrows[boardId].findIndex(
          (a) => a.from === startSquare && a.to === square.dataset.square,
        );
        if (existingIndex !== -1) {
          boardArrows[boardId].splice(existingIndex, 1);
          const svg = document.getElementById(boardId + "-svg");
          if (svg) svg.innerHTML = "";
          boardArrows[boardId].forEach((a) =>
            drawArrow(boardId, a.from, a.to, getFlipped(), false),
          );
        } else {
          boardArrows[boardId].push({
            from: startSquare,
            to: square.dataset.square,
          });
          drawArrow(
            boardId,
            startSquare,
            square.dataset.square,
            getFlipped(),
            false,
          );
        }
      }
      startSquare = null;
      const svg = document.getElementById(boardId + "-svg");
      if (svg) svg.querySelectorAll(".temp-arrow").forEach((el) => el.remove());
    }
  });
  board.addEventListener("click", (e) => {
    if (e.button === 2) return;
    const svg = document.getElementById(boardId + "-svg");
    if (svg) svg.innerHTML = "";
    boardArrows[boardId] = [];
  });
  window.addEventListener("mouseup", (e) => {
    if (e.button === 2) {
      startSquare = null;
      const svg = document.getElementById(boardId + "-svg");
      if (svg) svg.querySelectorAll(".temp-arrow").forEach((el) => el.remove());
    }
  });
}

function drawArrow(boardId, from, to, flipped, isTemp) {
  const boardEl = document.getElementById(boardId),
    svg = document.getElementById(boardId + "-svg");
  if (!boardEl || !svg) return;
  if (isTemp) svg.querySelectorAll(".temp-arrow").forEach((el) => el.remove());

  const fromEl = boardEl.querySelector(`[data-square="${from}"]`),
    toEl = boardEl.querySelector(`[data-square="${to}"]`);
  if (!fromEl || !toEl) return;

  const boardRect = boardEl.getBoundingClientRect(),
    fromRect = fromEl.getBoundingClientRect(),
    toRect = toEl.getBoundingClientRect();
  const x1 = fromRect.left - boardRect.left + fromRect.width / 2,
    y1 = fromRect.top - boardRect.top + fromRect.height / 2;
  const x2 = toRect.left - boardRect.left + toRect.width / 2,
    y2 = toRect.top - boardRect.top + toRect.height / 2;
  const dx = x2 - x1,
    dy = y2 - y1,
    size = 90;
  let isKnight = false,
    cornerX = x1,
    cornerY = y1;

  if (
    (Math.abs(dx) === size * 2 && Math.abs(dy) === size) ||
    (Math.abs(dx) === size && Math.abs(dy) === size * 2)
  ) {
    isKnight = true;
    if (Math.abs(dx) > Math.abs(dy)) {
      cornerX = x1;
      cornerY = y1 + Math.sign(dy) * size;
    } else {
      cornerX = x1 + Math.sign(dx) * size;
      cornerY = y1;
    }
  }

  const color = isTemp ? "rgba(255, 255, 0, 0.6)" : "rgba(255, 165, 0, 0.8)";
  let pathData = "",
    angle;
  if (isKnight) {
    pathData = `M ${x1} ${y1} L ${cornerX} ${cornerY} L ${x2} ${y2}`;
    angle = Math.atan2(y2 - cornerY, x2 - cornerX);
  } else {
    pathData = `M ${x1} ${y1} L ${x2} ${y2}`;
    angle = Math.atan2(y2 - y1, x2 - x1);
  }

  const headLen = 25,
    headAngle = Math.PI / 6;
  const x3 = x2 - headLen * Math.cos(angle - headAngle),
    y3 = y2 - headLen * Math.sin(angle - headAngle);
  const x4 = x2 - headLen * Math.cos(angle + headAngle),
    y4 = y2 - headLen * Math.sin(angle + headAngle);

  const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
  path.setAttribute("d", pathData);
  path.setAttribute("stroke", color);
  path.setAttribute("stroke-width", "10");
  path.setAttribute("stroke-linecap", "round");
  path.setAttribute("stroke-linejoin", "round");
  path.setAttribute("fill", "none");
  if (isTemp) path.classList.add("temp-arrow");

  const polygon = document.createElementNS(
    "http://www.w3.org/2000/svg",
    "polygon",
  );
  polygon.setAttribute("points", `${x2},${y2} ${x3},${y3} ${x4},${y4}`);
  polygon.setAttribute("fill", color);
  if (isTemp) polygon.classList.add("temp-arrow");

  svg.appendChild(path);
  svg.appendChild(polygon);
}

// STATUS UPDATER
function updateStatusText(elementId, puzzle, chessObj) {
  let el = document.getElementById(elementId);
  if (!el) return;
  if (!puzzle) {
    el.innerText = "Loading puzzle...";
    return;
  }
  let req = parseInt(puzzle.movesRequired) || 0;
  let turn = chessObj.turn() === "w" ? "White" : "Black";

  if (chessObj.game_over()) {
    if (chessObj.in_checkmate())
      el.innerText = `Checkmate! ${chessObj.turn() === "w" ? "Black" : "White"} wins.`;
    else el.innerText = `Game Over: Draw`;
  } else if (req <= 0) el.innerText = "Puzzle Solved!";
  else
    el.innerText = `${turn} to move (${req} move${req !== 1 ? "s" : ""} left)`;
}

function updateSolverStatus() {
  updateStatusText("solver-turn-text", activePuzzle, chess);
}

// MAKER
function loadMakerFEN() {
  let input = document.getElementById("fen-input").value;
  let parsed = parseCustomFEN(input);
  makerBoardFlipped = parsed.flip;
  chess.load(parsed.standardFen);
  renderBoard("maker-board", parsed.standardFen, makerBoardFlipped);
  if (stockfish) {
    stockfish.postMessage(`position fen ${parsed.standardFen}`);
    stockfish.postMessage("go depth 10");
  }
}

function toggleMakerFlip() {
  makerBoardFlipped = !makerBoardFlipped;
  let input = document.getElementById("fen-input").value;
  let parsed = parseCustomFEN(input);
  document.getElementById("fen-input").value =
    parsed.standardFen + (makerBoardFlipped ? " B" : " W");
  renderBoard("maker-board", parsed.standardFen, makerBoardFlipped);
}

function loadMakerFromCode() {
  let code = document.getElementById("maker-load-code").value;
  try {
    let data = JSON.parse(decodeString(code));
    let puzzleData = {};
    if (Array.isArray(data)) {
      puzzleData = {
        title: data[0] || "Untitled",
        fen: data[1],
        req: data[2],
        pre: data[3],
        top: data[4],
        hin: data[5],
        sol: data[6],
        wro: data[7],
        botInc: data[8],
      };
    } else {
      puzzleData = {
        title: data.title,
        fen: data.fen || data.FEN,
        req: data.req || data.movesRequired,
        pre: data.pre || data.preMoves,
        top: data.top || data.topMoves,
        hin: data.hin || data.hints,
        sol: data.sol || data.solution,
        wro: data.wro || data.wrong,
        botInc: data.botInc || data.botMovesIncluded,
      };
    }
    document.getElementById("fen-input").value =
      puzzleData.fen ||
      "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
    document.getElementById("moves-required").value = puzzleData.req || 1;
    document.getElementById("pre-moves").value = puzzleData.pre || "";
    document.getElementById("top-moves").value = puzzleData.top || 1;
    document.getElementById("hints-input").value = puzzleData.hin || "";
    document.getElementById("solution-input").value = puzzleData.sol || "";
    document.getElementById("wrong-input").value = puzzleData.wro || "";
    document.getElementById("bot-moves-included").checked =
      puzzleData.botInc || false;
    loadMakerFEN();
    console.log("Puzzle loaded into Maker!");
  } catch (e) {
    console.error("Invalid code!");
  }
}

function togglePreview() {
  if (isMakerPreviewing) stopPreview();
  else startPreview();
}

function startPreview() {
  isMakerPreviewing = true;
  document.getElementById("btn-preview").innerText = "Stop Preview";
  document.getElementById("btn-preview").style.backgroundColor = "#f44336";

  let fenInput = document.getElementById("fen-input").value;
  let parsedFen = parseCustomFEN(fenInput);
  makerBoardFlipped = parsedFen.flip;

  let solStr = document.getElementById("solution-input").value;
  let parsedSol = parseSolutionString(solStr);
  previewInitialPaths = JSON.parse(JSON.stringify(parsedSol.paths));
  puzzleExplanation = parsedSol.explanation;
  previewActivePathIndex = -1;

  activePuzzle = {
    id: -1,
    title: "Preview",
    fen: fenInput,
    movesRequired:
      parseInt(document.getElementById("moves-required").value) || 1,
    preMoves: document.getElementById("pre-moves").value,
    topMoves: parseInt(document.getElementById("top-moves").value) || 1,
    hints: document.getElementById("hints-input").value,
    solution: solStr,
    wrong: document.getElementById("wrong-input").value,
    botMovesIncluded: document.getElementById("bot-moves-included").checked,
  };

  solutionPaths = parsedSol.paths;
  currentPathIndex = -1;
  currentMoveIndex = 0;
  chess.load(parsedFen.standardFen);
  let hintsArr = activePuzzle.hints
    ? activePuzzle.hints.split(",").filter((h) => h.trim() !== "")
    : [];
  originalHintCount = hintsArr.length;
  hintCount = originalHintCount;
  originalMovesRequired = parseInt(activePuzzle.movesRequired) || 1;
  activePuzzle.movesRequired = originalMovesRequired;
  renderBoard("maker-board", chess.fen(), makerBoardFlipped, null);

  let finishPreview = () => {
    originalSolverFen = chess.fen();
    activePuzzle.movesRequired = originalMovesRequired;
    updateStatusText("maker-preview-status", activePuzzle, chess);
    evaluatePosition(chess.fen(), 2000);
  };

  if (activePuzzle.preMoves && activePuzzle.preMoves.trim() !== "") {
    document.getElementById("maker-preview-status").innerText =
      "Playing pre-moves...";
    document.getElementById("maker-board").style.pointerEvents = "none";
    playPreMoves(
      activePuzzle.preMoves,
      "maker-board",
      makerBoardFlipped,
      () => {
        document.getElementById("maker-board").style.pointerEvents = "auto";
        finishPreview();
      },
    );
  } else finishPreview();
}

function stopPreview() {
  isMakerPreviewing = false;
  document.getElementById("btn-preview").innerText = "Preview Puzzle";
  document.getElementById("btn-preview").style.backgroundColor = "#4CAF50";
  document.getElementById("maker-preview-status").innerText = "";
  document.getElementById("maker-board").style.pointerEvents = "auto";
  activePuzzle = null;
  previewActivePathIndex = -1;
  loadMakerFEN();
}

function updatePreviewSolutionText(moveUci) {
  let textarea = document.getElementById("solution-input");
  if (previewActivePathIndex === -1) {
    let existingIdx = previewInitialPaths.findIndex(
      (p) => p.length > 0 && p[0] === moveUci,
    );
    if (existingIdx !== -1) {
      previewActivePathIndex = existingIdx;
      previewInitialPaths[existingIdx] = [moveUci];
    } else {
      previewInitialPaths.push([moveUci]);
      previewActivePathIndex = previewInitialPaths.length - 1;
    }
  } else previewInitialPaths[previewActivePathIndex].push(moveUci);

  let newSolStr = formatSolutionString(previewInitialPaths, puzzleExplanation);
  textarea.value = newSolStr;
  activePuzzle.solution = newSolStr;
  solutionPaths = previewInitialPaths;
  currentPathIndex = previewActivePathIndex;
  currentMoveIndex = previewInitialPaths[previewActivePathIndex].length;
}

function generateCode() {
  let fenInput = document.getElementById("fen-input").value;
  let parsed = parseCustomFEN(fenInput);
  let finalFen = parsed.standardFen + (makerBoardFlipped ? " B" : " W");
  let finalSolution = document.getElementById("solution-input").value;

  let puzzleArray = [
    "Custom Puzzle",
    finalFen,
    parseInt(document.getElementById("moves-required").value) || 1,
    document.getElementById("pre-moves").value,
    parseInt(document.getElementById("top-moves").value) || 1,
    document.getElementById("hints-input").value,
    finalSolution,
    document.getElementById("wrong-input").value,
    document.getElementById("bot-moves-included").checked,
  ];

  document.getElementById("generated-code").value = encodeString(
    JSON.stringify(puzzleArray),
  );
}

function copyGeneratedCode() {
  let code = document.getElementById("generated-code").value;
  if (!code) return;
  navigator.clipboard.writeText(code);
  console.log("Code copied to clipboard!");
}

// LIST LOGIC
function getSavedPuzzles() {
  let s = localStorage.getItem("chessPuzzles");
  return s ? JSON.parse(s) : [];
}

function renderPuzzleList() {
  const container = document.getElementById("puzzle-list-container");
  if (!container) return;
  container.innerHTML = "";
  let puzzles = getSavedPuzzles(),
    completed = 0;

  puzzles.forEach((p) => {
    if (p.completed) completed++;
    let div = document.createElement("div");
    div.className = `puzzle-item ${!p.completed ? "incomplete" : ""}`;
    let leftSide = document.createElement("div");
    leftSide.className = "puzzle-item-left";
    let star = document.createElement("span");
    star.className = p.favorite ? "star favorited" : "star";
    star.innerText = p.favorite ? "★" : "☆";
    star.onclick = (e) => {
      e.stopPropagation();
      p.favorite = !p.favorite;
      localStorage.setItem("chessPuzzles", JSON.stringify(puzzles));
      renderPuzzleList();
    };
    let title = document.createElement("span");
    title.className = "title";
    title.innerText = p.title || "Untitled";
    leftSide.appendChild(star);
    leftSide.appendChild(title);

    let actionsDiv = document.createElement("div");
    actionsDiv.style.display = "flex";
    actionsDiv.style.alignItems = "center";
    actionsDiv.style.gap = "10px";
    let copyBtn = document.createElement("button");
    copyBtn.className = "action-btn";
    copyBtn.innerHTML = '<img src="images/copy.svg" alt="Copy">';
    copyBtn.onclick = (e) => {
      e.stopPropagation();
      let arr = [
        p.title,
        p.fen,
        p.movesRequired,
        p.preMoves,
        p.topMoves,
        p.hints,
        p.solution,
        p.wrong,
        p.botMovesIncluded,
      ];
      navigator.clipboard.writeText(encodeString(JSON.stringify(arr)));
      console.log("Code copied to clipboard!");
    };
    let deleteBtn = document.createElement("button");
    deleteBtn.className = "delete-btn";
    deleteBtn.innerText = "✖";
    deleteBtn.onclick = (e) => {
      e.stopPropagation();
      if (confirm("Delete this puzzle?")) {
        let newPuzzles = puzzles.filter((x) => x.id !== p.id);
        localStorage.setItem("chessPuzzles", JSON.stringify(newPuzzles));
        renderPuzzleList();
      }
    };
    actionsDiv.appendChild(copyBtn);
    actionsDiv.appendChild(deleteBtn);
    div.appendChild(leftSide);
    div.appendChild(actionsDiv);
    div.onclick = () => startSolver(p);
    container.appendChild(div);
  });
  document.getElementById("completion-status").innerText =
    `Completed: ${completed} | Not Completed: ${puzzles.length - completed}`;
}

function loadPuzzleFromCode() {
  let code = document.getElementById("load-code-input").value;
  try {
    let data = JSON.parse(decodeString(code));
    let puzzleData = {};
    if (Array.isArray(data)) {
      puzzleData = {
        title: data[0] || "Untitled",
        fen: data[1],
        movesRequired: parseInt(data[2]) || 1,
        preMoves: data[3],
        topMoves: parseInt(data[4]) || 1,
        hints: data[5],
        solution: data[6],
        wrong: data[7],
        botMovesIncluded: data[8],
      };
    } else {
      puzzleData = {
        title: data.title || "Untitled",
        fen: data.fen || data.FEN,
        movesRequired: parseInt(data.req || data.movesRequired) || 1,
        preMoves: data.pre || data.preMoves,
        topMoves: parseInt(data.top || data.topMoves) || 1,
        hints: data.hin || data.hints,
        solution: data.sol || data.solution,
        wrong: data.wro || data.wrong,
        botMovesIncluded: data.botInc || data.botMovesIncluded,
      };
    }
    let puzzles = getSavedPuzzles();
    let baseTitle = puzzleData.title || "Untitled";
    let newTitle = baseTitle;
    let counter = 1;
    while (puzzles.some((p) => p.title === newTitle)) {
      newTitle = `${baseTitle} (${counter})`;
      counter++;
    }
    puzzleData.title = newTitle;
    puzzleData.id = Date.now();
    puzzleData.completed = false;
    puzzleData.favorite = false;
    puzzles.push(puzzleData);
    localStorage.setItem("chessPuzzles", JSON.stringify(puzzles));
    console.log("Puzzle Loaded!");
    renderPuzzleList();
    document.getElementById("load-code-input").value = "";
  } catch (e) {
    console.error("Invalid code!");
  }
}

// SOLVER
function startSolver(puzzle) {
  activePuzzle = puzzle;
  activePuzzle.botMovesIncluded =
    activePuzzle.botMovesIncluded === true || activePuzzle.botInc === true;
  let parsedFen = parseCustomFEN(puzzle.fen);
  solverBoardFlipped = parsedFen.flip;
  document.getElementById("solver-title-input").value =
    puzzle.title || "Untitled";
  document.getElementById("solver-wrong-text").innerText = puzzle.wrong
    ? `What went wrong: ${puzzle.wrong}`
    : "";

  let parsedSol = parseSolutionString(puzzle.solution);
  solutionPaths = parsedSol.paths;
  puzzleExplanation = parsedSol.explanation;
  currentPathIndex = -1;
  currentMoveIndex = 0;

  chess.load(parsedFen.standardFen);
  let hintsArr = puzzle.hints
    ? puzzle.hints.split(",").filter((h) => h.trim() !== "")
    : [];
  originalHintCount = hintsArr.length;
  hintCount = originalHintCount;
  activePuzzle.movesRequired = parseInt(puzzle.movesRequired) || 1;
  originalMovesRequired = activePuzzle.movesRequired;

  nav("view-solver");
  renderBoard("solver-board", chess.fen(), solverBoardFlipped, null);

  let finishSetup = () => {
    originalSolverFen = chess.fen();
    resetSolverUI();
    evaluatePosition(chess.fen());
  };

  if (puzzle.preMoves && puzzle.preMoves.trim() !== "") {
    document.getElementById("solver-turn-text").innerText =
      "Playing pre-moves...";
    document.getElementById("solver-board").style.pointerEvents = "none";
    playPreMoves(puzzle.preMoves, "solver-board", solverBoardFlipped, () => {
      document.getElementById("solver-board").style.pointerEvents = "auto";
      finishSetup();
    });
  } else finishSetup();
}

function resetSolverUI() {
  hintCount = originalHintCount;
  document.getElementById("btn-hint").innerText = `💡 Hint (${hintCount})`;
  document.getElementById("btn-hint").disabled = hintCount === 0;
  document.getElementById("hint-bubble").classList.add("hidden");
  document.getElementById("explanation-box").classList.add("hidden");
  document.getElementById("explanation-box").value = "";
  selectedSquare = null;
  isBotThinking = false;
  activePuzzle.movesRequired = originalMovesRequired;
  currentPathIndex = -1;
  currentMoveIndex = 0;
  document
    .querySelectorAll(".square")
    .forEach((s) =>
      s.classList.remove("selected", "highlight-last", "wrong-move"),
    );
  updateSolverStatus();
}

function resetSolver() {
  if (!activePuzzle) return;
  chess.load(originalSolverFen);
  renderBoard("solver-board", chess.fen(), solverBoardFlipped, null);
  resetSolverUI();
  evaluatePosition(chess.fen());
}

function exitSolver() {
  nav("view-list");
  activePuzzle = null;
  isBotThinking = false;
}

const titleInput = document.getElementById("solver-title-input");
if (titleInput) {
  titleInput.addEventListener("change", function () {
    if (!activePuzzle) return;
    let newTitle = this.value.trim() || "Untitled";
    let puzzles = getSavedPuzzles();
    let baseTitle = newTitle.replace(/\s\(\d+\)$/, "");
    let counter = 1;
    let isDuplicate = puzzles.some(
      (p) => p.title === newTitle && p.id !== activePuzzle.id,
    );
    while (isDuplicate) {
      newTitle = `${baseTitle} (${counter})`;
      counter++;
      isDuplicate = puzzles.some(
        (p) => p.title === newTitle && p.id !== activePuzzle.id,
      );
    }
    activePuzzle.title = newTitle;
    this.value = newTitle;
    let pIndex = puzzles.findIndex((p) => p.id === activePuzzle.id);
    if (pIndex !== -1) {
      puzzles[pIndex].title = newTitle;
      localStorage.setItem("chessPuzzles", JSON.stringify(puzzles));
    }
  });
}

async function handleBoardClick(e, boardId) {
  if (e.button === 2 || dragState.justDragged) return;
  if (
    !activePuzzle ||
    isBotThinking ||
    activePuzzle.movesRequired <= 0 ||
    chess.game_over()
  )
    return;
  const square = e.target.closest(".square");
  if (!square) return;
  let playerColor = activePuzzle.fen.split(" ")[1];
  if (chess.turn() !== playerColor) return;

  if (!selectedSquare) {
    const piece = chess.get(square.dataset.square);
    if (piece && piece.color === chess.turn()) {
      document
        .querySelectorAll(`#${boardId} .square`)
        .forEach((s) => s.classList.remove("selected"));
      selectedSquare = square.dataset.square;
      square.classList.add("selected");
    }
  } else {
    const from = selectedSquare,
      to = square.dataset.square;
    selectedSquare = null;
    document
      .querySelectorAll(`#${boardId} .square`)
      .forEach((s) => s.classList.remove("selected"));
    await attemptMove(from, to, boardId);
  }
}

async function attemptMove(from, to, boardId) {
  let flipped =
    boardId === "maker-board" ? makerBoardFlipped : solverBoardFlipped;
  let fenBefore = chess.fen();
  let move = null;
  try {
    move = chess.move({ from: from, to: to, promotion: "q" });
  } catch (err) {
    document.querySelectorAll(`#${boardId} .square`).forEach((s) => {
      if (s.dataset.square === from || s.dataset.square === to)
        s.classList.add("wrong-move");
    });
    setTimeout(() => {
      document
        .querySelectorAll(`#${boardId} .square`)
        .forEach((s) => s.classList.remove("wrong-move"));
    }, 500);
    return;
  }

  if (!move) {
    document.querySelectorAll(`#${boardId} .square`).forEach((s) => {
      if (s.dataset.square === from || s.dataset.square === to)
        s.classList.add("wrong-move");
    });
    setTimeout(() => {
      document
        .querySelectorAll(`#${boardId} .square`)
        .forEach((s) => s.classList.remove("wrong-move"));
    }, 500);
    return;
  }

  let userMoveUci =
    move.from + move.to + (move.promotion ? move.promotion : "");
  let isValid = false;

  if (isMakerPreviewing) {
    updateStatusText("maker-preview-status", activePuzzle, chess);
    isValid = true;
  } else {
    document.getElementById("solver-turn-text").innerText = "Checking move...";
    if (solutionPaths.length > 0) {
      if (currentPathIndex === -1) {
        for (let i = 0; i < solutionPaths.length; i++) {
          if (
            solutionPaths[i].length > 0 &&
            solutionPaths[i][0].toLowerCase() === userMoveUci.toLowerCase()
          ) {
            isValid = true;
            currentPathIndex = i;
            currentMoveIndex = 1;
            break;
          }
        }
      } else {
        if (currentMoveIndex < solutionPaths[currentPathIndex].length) {
          if (
            solutionPaths[currentPathIndex][currentMoveIndex].toLowerCase() ===
            userMoveUci.toLowerCase()
          ) {
            isValid = true;
            currentMoveIndex++;
          }
        }
      }
    } else {
      let topMoves = await getEngineMoves(
        fenBefore,
        activePuzzle.topMoves || 1,
      );
      let validMovesCount = Math.min(
        topMoves.length,
        activePuzzle.topMoves || 1,
      );
      for (let i = 0; i < validMovesCount; i++) {
        if (
          topMoves[i] &&
          topMoves[i].toLowerCase() === userMoveUci.toLowerCase()
        ) {
          isValid = true;
          break;
        }
      }
    }
  }

  if (!isValid) {
    playSound(move);
    renderBoard(boardId, chess.fen(), flipped, move);
    document.querySelectorAll(`#${boardId} .square`).forEach((s) => {
      if (s.dataset.square === from || s.dataset.square === to)
        s.classList.add("wrong-move");
    });
    setTimeout(() => {
      chess.load(fenBefore);
      renderBoard(boardId, chess.fen(), flipped, null);
      evaluatePosition(fenBefore);
      document
        .querySelectorAll(`#${boardId} .square`)
        .forEach((s) => s.classList.remove("wrong-move"));
      if (isMakerPreviewing)
        updateStatusText("maker-preview-status", activePuzzle, chess);
      else updateSolverStatus();
    }, 500);
    return;
  }

  playSound(move);
  renderBoard(boardId, chess.fen(), flipped, move);
  activePuzzle.movesRequired--;

  if (isMakerPreviewing) {
    updatePreviewSolutionText(userMoveUci);
    updateStatusText("maker-preview-status", activePuzzle, chess);
  } else {
    updateSolverStatus();
  }

  if (chess.game_over() || activePuzzle.movesRequired === 0) {
    if (activePuzzle.movesRequired === 0 && boardId === "solver-board") {
      if (!activePuzzle.completed) {
        sounds.notify.play().catch((e) => {});
        activePuzzle.completed = true;
        let puzzles = getSavedPuzzles();
        let p = puzzles.find((x) => x.id === activePuzzle.id);
        if (p) p.completed = true;
        localStorage.setItem("chessPuzzles", JSON.stringify(puzzles));
      }
    }
    evaluatePosition(chess.fen());
    showExplanationIfAny(activePuzzle);
  } else {
    if (isMakerPreviewing)
      document.getElementById("maker-preview-status").innerText =
        "Stockfish thinking...";
    else
      document.getElementById("solver-turn-text").innerText =
        "Stockfish thinking...";

    if (activePuzzle.botMovesIncluded && currentPathIndex !== -1) {
      let nextMoveStr = solutionPaths[currentPathIndex][currentMoveIndex];
      if (nextMoveStr) {
        setTimeout(() => {
          try {
            let botMove = chess.move({
              from: nextMoveStr.substring(0, 2),
              to: nextMoveStr.substring(2, 4),
              promotion: "q",
            });
            if (botMove) {
              playSound(botMove);
              renderBoard(boardId, chess.fen(), flipped, botMove);
              currentMoveIndex++;
              if (isMakerPreviewing) {
                updatePreviewSolutionText(nextMoveStr);
                updateStatusText("maker-preview-status", activePuzzle, chess);
              } else {
                updateSolverStatus();
              }
              evaluatePosition(chess.fen());
            }
          } catch (e) {
            if (isMakerPreviewing)
              updateStatusText("maker-preview-status", activePuzzle, chess);
            else updateSolverStatus();
          }
        }, 1000);
      } else {
        isBotThinking = true;
        let botMoves = await getEngineMoves(chess.fen(), 1);
        isBotThinking = false;
        if (botMoves.length > 0 && botMoves[0] !== "(none)") {
          let bestMove = botMoves[0];
          setTimeout(() => {
            try {
              let botMove = chess.move({
                from: bestMove.substring(0, 2),
                to: bestMove.substring(2, 4),
                promotion: "q",
              });
              if (botMove) {
                playSound(botMove);
                renderBoard(boardId, chess.fen(), flipped, botMove);
                if (isMakerPreviewing) {
                  updatePreviewSolutionText(bestMove);
                  updateStatusText("maker-preview-status", activePuzzle, chess);
                } else {
                  updateSolverStatus();
                }
                evaluatePosition(chess.fen());
              }
            } catch (e) {
              if (isMakerPreviewing)
                updateStatusText("maker-preview-status", activePuzzle, chess);
              else updateSolverStatus();
            }
          }, 1000);
        } else {
          if (isMakerPreviewing)
            updateStatusText("maker-preview-status", activePuzzle, chess);
          else updateSolverStatus();
        }
      }
    } else {
      isBotThinking = true;
      let botMoves = await getEngineMoves(chess.fen(), 1);
      isBotThinking = false;
      if (botMoves.length > 0 && botMoves[0] !== "(none)") {
        let bestMove = botMoves[0];
        setTimeout(() => {
          try {
            let botMove = chess.move({
              from: bestMove.substring(0, 2),
              to: bestMove.substring(2, 4),
              promotion: "q",
            });
            if (botMove) {
              playSound(botMove);
              renderBoard(boardId, chess.fen(), flipped, botMove);
              if (isMakerPreviewing) {
                updatePreviewSolutionText(bestMove);
                updateStatusText("maker-preview-status", activePuzzle, chess);
              } else {
                updateSolverStatus();
              }
              evaluatePosition(chess.fen());
            }
          } catch (e) {
            if (isMakerPreviewing)
              updateStatusText("maker-preview-status", activePuzzle, chess);
            else updateSolverStatus();
          }
        }, 1000);
      } else {
        if (isMakerPreviewing)
          updateStatusText("maker-preview-status", activePuzzle, chess);
        else updateSolverStatus();
      }
    }
  }
}

const solverBoardEl = document.getElementById("solver-board");
if (solverBoardEl)
  solverBoardEl.addEventListener("click", (e) =>
    handleBoardClick(e, "solver-board"),
  );

const makerBoardEl = document.getElementById("maker-board");
if (makerBoardEl)
  makerBoardEl.addEventListener("click", (e) => {
    if (isMakerPreviewing) handleBoardClick(e, "maker-board");
  });

function showHint() {
  if (hintCount <= 0 || !activePuzzle || !activePuzzle.hints) return;
  let hintsArr = activePuzzle.hints.split(",").filter((h) => h.trim() !== "");
  let hintsUsed = originalHintCount - hintCount;
  let hintText =
    hintsArr[hintsUsed] || hintsArr[hintsArr.length - 1] || "No hint available";
  document.getElementById("hint-text").innerText = hintText.trim();
  document.getElementById("hint-bubble").classList.remove("hidden");
  hintCount--;
  document.getElementById("btn-hint").innerText = `💡 Hint (${hintCount})`;
  if (hintCount === 0) document.getElementById("btn-hint").disabled = true;
}

async function showSolution() {
  if (!activePuzzle) return;
  chess.load(originalSolverFen);
  renderBoard("solver-board", chess.fen(), solverBoardFlipped, null);
  const svg = document.getElementById("solver-board-svg");
  if (svg) svg.innerHTML = "";
  boardArrows["solver-board"] = [];
  document.getElementById("explanation-box").classList.add("hidden");
  document.getElementById("explanation-box").value = "";

  let parsedSol = parseSolutionString(activePuzzle.solution);
  let path = parsedSol.paths.length > 0 ? parsedSol.paths[0] : [];
  let explanation = parsedSol.explanation;

  if (path.length === 0) {
    if (explanation) {
      document.getElementById("explanation-box").value = explanation;
      document.getElementById("explanation-box").classList.remove("hidden");
    }
    return;
  }

  let userMovesPlayed = 0,
    solIndex = 0,
    playerColor = activePuzzle.fen.split(" ")[1];

  const playStep = async () => {
    if (
      userMovesPlayed >= originalMovesRequired ||
      solIndex >= path.length ||
      chess.game_over()
    ) {
      if (explanation) {
        document.getElementById("explanation-box").value = explanation;
        document.getElementById("explanation-box").classList.remove("hidden");
      }
      return;
    }
    let turn = chess.turn(),
      isPlayerTurn = turn === playerColor,
      m = path[solIndex];
    try {
      let move = chess.move({
        from: m.substring(0, 2),
        to: m.substring(2, 4),
        promotion: "q",
      });
      if (move) {
        playSound(move);
        renderBoard("solver-board", chess.fen(), solverBoardFlipped, move);
        evaluatePosition(chess.fen());
        solIndex++;
        if (isPlayerTurn) userMovesPlayed++;
      }
    } catch (e) {
      console.error("Solution move failed", m, e);
    }
    setTimeout(playStep, 700);
  };
  playStep();
}

window.onload = () => {
  if (typeof initPalette === "function") initPalette();
  if (typeof loadMakerFEN === "function") loadMakerFEN();
  if (typeof setupArrows === "function") {
    setupArrows("maker-board", () => makerBoardFlipped);
    setupArrows("solver-board", () => solverBoardFlipped);
  }
  if (typeof setupDragging === "function") setupDragging();
};
