/* 
 * TRILHA A: RISC-V 2-ISSUE OOO TOMASULO SIMULATOR
 * Autor: Persona Expert Architect
 * Data: Novembro 2025
 */

// --- CONFIGURAÇÃO E CONSTANTES ---
const OPCODES = {
    ADD: 'ADD', SUB: 'SUB', AND: 'AND', OR: 'OR', XOR: 'XOR',
    SLT: 'SLT', ADDI: 'ADDI', LW: 'LW', SW: 'SW',
    BEQ: 'BEQ', BNE: 'BNE', JAL: 'JAL', JALR: 'JALR', NOP: 'NOP'
};

const EXEC_LATENCIES = {
    ALU: 1,
    LOAD: 2, // Base, + cache latency
    STORE: 1,
    BRANCH: 1
};

// --- CLASSES AUXILIARES (Hardware Components) ---

class Cache {
    constructor(name, latency, missPenalty) {
        this.name = name;
        this.latency = latency;
        this.missPenalty = missPenalty;
        // Simulação Simplificada de Conjuntos (2-way set associative, 64B block, 4KB size)
        this.sets = 32; 
        this.ways = 2;
        this.tags = new Array(this.sets).fill(null).map(() => new Array(this.ways).fill({ tag: -1, lru: 0, dirty: false }));
        
        // Métricas
        this.accessCount = 0;
        this.hitCount = 0;
        this.missCount = 0;
    }

    access(addr, isWrite = false) {
        this.accessCount++;
        const index = (addr >> 6) & 0x1F; // Bits 6-10 para índice (32 sets)
        const tag = addr >> 11;           // Resto para Tag

        const set = this.tags[index];
        let hit = false;
        let wayIdx = -1;

        // Check Hit
        for(let i=0; i<this.ways; i++) {
            if(set[i].tag === tag) {
                hit = true;
                wayIdx = i;
                break;
            }
        }

        if(hit) {
            this.hitCount++;
            set[wayIdx].lru = Date.now(); // Atualiza LRU
            if(isWrite) set[wayIdx].dirty = true;
            return { hit: true, cycles: this.latency };
        } else {
            this.missCount++;
            // Handle Replacement (LRU)
            let victimIdx = 0;
            let minLru = set.lru;
            for(let i=1; i<this.ways; i++) {
                if(set[i].lru < minLru) {
                    minLru = set[i].lru;
                    victimIdx = i;
                }
            }
            // Replace
            set[victimIdx] = { tag: tag, lru: Date.now(), dirty: isWrite };
            return { hit: false, cycles: this.latency + this.missPenalty };
        }
    }
}

class GsharePredictor {
    constructor() {
        this.ghr = 0; // Global History Register (10 bits)
        this.pht = new Uint8Array(1024).fill(1); // 2-bit counters (00, 01, 10, 11). Start Weakly Not Taken (1)
    }

    predict(pc) {
        const index = (pc ^ this.ghr) & 0x3FF; // XOR hash
        const counter = this.pht[index];
        return counter >= 2; // 2 or 3 means TAKEN
    }

    update(pc, taken) {
        const index = (pc ^ this.ghr) & 0x3FF;
        let counter = this.pht[index];
        if (taken) {
            if (counter < 3) counter++;
        } else {
            if (counter > 0) counter--;
        }
        this.pht[index] = counter;
        // Update GHR
        this.ghr = ((this.ghr << 1) | (taken? 1 : 0)) & 0x3FF;
    }
}

class Instruction {
    constructor(pc, text, op, rd, rs1, rs2, imm) {
        this.pc = pc;
        this.text = text;
        this.op = op;
        this.rd = rd; // 0-31
        this.rs1 = rs1;
        this.rs2 = rs2;
        this.imm = imm;
        
        // Pipeline State
        this.robTag = -1;
        this.predictedTaken = false;
        this.targetAddr = -1;
        this.executionCyclesLeft = 0;
        this.isReady = false; // Execution finished
        this.result = 0;
        this.memAddr = 0; // Calculated effective address
        this.isFlush = false; // Mark if this instruction is garbage due to flush
    }
}

// --- SIMULADOR CORE ---

class Simulator {
    constructor() {
        this.memory = new Int32Array(65536); // 256KB Main Memory
        this.regFile = new Int32Array(32).fill(0);
        this.pc = 0;
        this.clock = 0;
        
        // Microarchitecture Config
        this.robSize = 32;
        this.width = 2; // 2-issue
        
        // Structures
        this.rat = new Array(32).fill(-1); // -1 = In ARF, >=0 = ROB ID
        this.rob =; // Array acting as circular buffer
        this.rsALU =; // Array of {busy, op, vj, vk, qj, qk, rob, inst}
        this.rsLS =;  // Reservation Stations for Load/Store
        this.cdb = null; // Common Data Bus {tag, value}
        
        // Components
        this.l1i = new Cache("L1I", 1, 10);
        this.l1d = new Cache("L1D", 2, 10);
        this.predictor = new GsharePredictor();
        
        // Program
        this.instructions =; // Loaded program memory map
        this.instructionsCommitted = 0;
        this.isRunning = false;
        this.logs =;

        this.initRS(8, 4); // 8 ALU RS, 4 LS RS
    }

    initRS(aluCount, lsCount) {
        this.rsALU = Array(aluCount).fill(null).map(() => ({ busy: false }));
        this.rsLS = Array(lsCount).fill(null).map(() => ({ busy: false }));
    }

    log(msg) {
        this.logs.push(`[Ciclo ${this.clock}] ${msg}`);
        const logEl = document.getElementById('sim-log');
        if(logEl) {
            logEl.textContent = this.logs.slice(-20).join('\n'); // Show last 20
            logEl.scrollTop = logEl.scrollHeight;
        }
    }

    loadProgram(text) {
        this.pc = 0;
        this.memory.fill(0);
        this.regFile.fill(0);
        this.rat.fill(-1);
        this.rob =;
        this.initRS(8, 4);
        this.clock = 0;
        this.instructionsCommitted = 0;
        this.logs =;
        
        // Simple Parser
        const lines = text.split('\n');
        let loadAddr = 0;
        this.instructions = {}; // Map Addr -> Instruction Template

        lines.forEach(line => {
            line = line.split(';').trim();
            if(!line) return;
            
            const parts = line.replace(/,/g, ' ').split(/\s+/);
            const op = parts.toUpperCase();
            let rd=0, rs1=0, rs2=0, imm=0;
            
            // Basic Parsing Logic (Simplified for brevity)
            if(.includes(op)) {
                rd = parseInt(parts.substring(1));
                rs1 = parseInt(parts.substring(1));
                rs2 = parseInt(parts.substring(1));
            } else if(.includes(op)) {
                rd = parseInt(parts.substring(1));
                rs1 = parseInt(parts.substring(1));
                imm = parseInt(parts);
            } else if(.includes(op)) {
                // Format: lw x6, 4(x0)
                const reg = parseInt(parts.substring(1));
                const offsetPart = parts;
                const immVal = parseInt(offsetPart.split('('));
                const rsVal = parseInt(offsetPart.split('(').replace(')','').substring(1));
                if(op === 'LW') { rd=reg; rs1=rsVal; imm=immVal; }
                else { rs2=reg; rs1=rsVal; imm=immVal; } // SW uses rs2 as source data
            } else if(.includes(op)) {
                rs1 = parseInt(parts.substring(1));
                rs2 = parseInt(parts.substring(1));
                imm = parseInt(parts); // Offset
            } else if(['JAL'].includes(op)) {
                rd = parseInt(parts.substring(1));
                imm = parseInt(parts);
            }
            
            this.instructions[loadAddr] = { text: line, op, rd, rs1, rs2, imm };
            loadAddr += 4; // 4 bytes per instruction
        });
        
        this.log("Programa carregado.");
        this.updateUI();
    }

    // --- PIPELINE STAGES (Executed in Reverse Order) ---

    step() {
        if(this.pc >= Object.keys(this.instructions).length * 4 && this.rob.length === 0) {
            this.isRunning = false;
            this.log("Execução finalizada.");
            return;
        }

        this.clock++;
        
        // 1. COMMIT (Retire)
        this.stageCommit();
        
        // 2. EXECUTE (ALUs & MEM) + CDB Broadcast
        this.stageExecute();
        
        // 3. ISSUE (Dispatch to RS/ROB)
        // Try to issue up to 2 instructions
        let issued = 0;
        // Fetch logic is integrated into Issue for this simplified event-model
        // Ideally Fetch puts into a queue, Issue takes from queue.
        // We will simulate Fetch/Decode/Issue in one block respecting constraints.
        
        while(issued < this.width) {
            if(!this.stageFetchAndIssue()) break;
            issued++;
        }
        
        this.updateUI();
    }

    stageCommit() {
        // Commit head of ROB if ready
        if(this.rob.length === 0) return;

        // Check head (index 0)
        const head = this.rob;
        
        if(head.isReady) {
            // Check for Branch Misprediction
            if(head.op === 'BEQ' |

| head.op === 'BNE') {
                const actualTaken = head.result === 1;
                // Update Predictor
                this.predictor.update(head.pc, actualTaken);
                
                if(actualTaken!== head.predictedTaken) {
                    this.log(`FLUSH! Branch em ${head.pc} mal previsto.`);
                    this.flushPipeline(head.targetAddr, actualTaken);
                    return; // Flush stops commit of subsequent instrs this cycle
                }
            }
            else if(head.op === 'JAL' |

| head.op === 'JALR') {
                // Jumps are always taken, check target correctness if BTB existed
                // Here we assume JAL is handled at Decode, but JALR needs execution.
            }

            // Write Result to ARF (if not a store/branch without link)
            if(head.rd!== 0 && head.op!== 'SW' && head.op!== 'BEQ' && head.op!== 'BNE') {
                this.regFile[head.rd] = head.result;
                // Update RAT: if RAT points to this ROB, set to -1 (value is in ARF)
                if(this.rat[head.rd] === head.robTag) {
                    this.rat[head.rd] = -1;
                }
            }

            // Handle Store Commit (Write to Memory/Cache)
            if(head.op === 'SW') {
                this.l1d.access(head.memAddr, true);
                this.memory[head.memAddr / 4] = head.result; // Simplified Memory Write
                this.log(`MEM[${head.memAddr}] = ${head.result}`);
            }

            // Remove from ROB
            this.rob.shift();
            this.instructionsCommitted++;
            
            // Allow 2 commits per cycle? "Trilha A" says ROB commit in order. 
            // Often restricted to 1 or 2. We allow 1 for simplicity or loop for width.
        }
    }

    flushPipeline(correctPC, taken) {
        // Clear ROB, RS, RAT
        this.rob =;
        this.initRS(8, 4);
        this.rat.fill(-1); // Simplification: In real HW, restore RAT from checkpoint or walk back ROB. 
                           // Here we assume "Architectural RAT" (ARF) is correct because we only commit valid instructions.
                           // So setting RAT to -1 forces next instructions to read from ARF.
        
        // Correct PC
        if(taken) {
            this.pc = correctPC;
        } else {
            // If we took it but shouldn't have, the correct PC is instruction after branch
            // This requires storing 'nextPC' in ROB entry.
            // For now, assuming provided correctPC argument is the *Next Valid PC*
             this.pc = correctPC; 
        }
    }

    stageExecute() {
        // Process RS entries
        // 1. Listen to CDB (Simulated by checking ROB values for operands that were waiting)
        // In real HW, CDB happens at end of cycle. Here we check readiness.

       .forEach(rs => {
            if(!rs.busy) return;
            const inst = rs.inst;
            
            // Check operands
            if(rs.qj!== -1) {
                // Check if producer ROB is ready
                const producer = this.rob.find(r => r.robTag === rs.qj);
                if(producer && producer.isReady) {
                    rs.vj = producer.result;
                    rs.qj = -1;
                }
            }
            if(rs.qk!== -1) {
                const producer = this.rob.find(r => r.robTag === rs.qk);
                if(producer && producer.isReady) {
                    rs.vk = producer.result;
                    rs.qk = -1;
                }
            }

            // If ready to execute
            if(rs.qj === -1 && rs.qk === -1 &&!inst.isReady && inst.executionCyclesLeft > 0) {
                // Execute Logic
                if(inst.executionCyclesLeft === inst.totalCycles) {
                    // Start of execution - Memory Access Calculation
                    if(inst.op === 'LW' |

| inst.op === 'SW') {
                         inst.memAddr = rs.vj + inst.imm;
                    }
                }
                
                inst.executionCyclesLeft--;
                
                if(inst.executionCyclesLeft === 0) {
                    // Compute Result
                    let val = 0;
                    switch(inst.op) {
                        case 'ADD': val = rs.vj + rs.vk; break;
                        case 'SUB': val = rs.vj - rs.vk; break;
                        case 'ADDI': val = rs.vj + inst.imm; break;
                        case 'LW': 
                            // Check LSQ for forwarding would go here
                            const cacheRes = this.l1d.access(inst.memAddr, false);
                            if(!cacheRes.hit) {
                                // Add penalty? For simplicity, we assume latency covers it or stall.
                                // In detailed sim, we would keep executionCyclesLeft > 0
                            }
                            val = this.memory[inst.memAddr / 4] |

| 0; 
                            break;
                        case 'SW': val = rs.vk; break; // Value to store
                        case 'BEQ': val = (rs.vj === rs.vk)? 1 : 0; break;
                        case 'BNE': val = (rs.vj!== rs.vk)? 1 : 0; break;
                        //... others
                    }
                    inst.result = val;
                    inst.isReady = true;
                    
                    // Broadcast to ROB
                    const robEntry = this.rob.find(r => r.robTag === inst.robTag);
                    if(robEntry) {
                        robEntry.result = val;
                        robEntry.isReady = true;
                        if(inst.op === 'BEQ' |

| inst.op === 'BNE') {
                            // Target address calculation for flush logic
                            robEntry.targetAddr = (val === 1)? inst.pc + inst.imm : inst.pc + 4;
                            // If NOT taken, target is PC+4. If Taken, target is PC+imm.
                            // Correction logic handled in Commit.
                        }
                    }
                    
                    rs.busy = false; // Free RS
                    this.log(`EXEC: ${inst.text} -> Result: ${val}`);
                }
            }
        });
    }

    stageFetchAndIssue() {
        // 1. Check Capacity (ROB, RS)
        if(this.rob.length >= this.robSize) return false;
        
        // Find RS
        const template = this.instructions[this.pc];
        if(!template) return false; // End of code

        let rs = null;
        let isLS =.includes(template.op);
        
        if(isLS) rs = this.rsLS.find(r =>!r.busy);
        else rs = this.rsALU.find(r =>!r.busy);
        
        if(!rs) return false; // No RS available

        // 2. Fetch (L1I Access)
        const cacheRes = this.l1i.access(this.pc);
        if(!cacheRes.hit) {
            // Simulate Stall for Miss Penalty?
            // For now, we log it.
            this.log(`L1I MISS em ${this.pc}`);
        }

        // 3. Create Instruction Instance
        const inst = new Instruction(
            this.pc, template.text, template.op, 
            template.rd, template.rs1, template.rs2, template.imm
        );
        
        // Assign ROB Tag
        // Generate a unique incremental tag. 
        // In loop buffer, index is tag.
        // We use a global counter for ID, mapped to ROB array index.
        const robTag = this.instructionsCommitted + this.rob.length + 1; // Simplified ID
        inst.robTag = robTag;
        
        // 4. Rename (Read RAT/ARF)
        // Source 1
        let qj = -1, vj = 0;
        if(template.rs1!== undefined) {
            if(this.rat[template.rs1]!== -1) {
                // Check if value is ready in ROB
                const producer = this.rob.find(r => r.robTag === this.rat[template.rs1]);
                if(producer && producer.isReady) {
                    vj = producer.result;
                } else {
                    qj = this.rat[template.rs1];
                }
            } else {
                vj = this.regFile[template.rs1];
            }
        }
        
        // Source 2
        let qk = -1, vk = 0;
        if(template.rs2!== undefined) { // Registers
             if(this.rat[template.rs2]!== -1) {
                const producer = this.rob.find(r => r.robTag === this.rat[template.rs2]);
                if(producer && producer.isReady) {
                    vk = producer.result;
                } else {
                    qk = this.rat[template.rs2];
                }
            } else {
                vk = this.regFile[template.rs2];
            }
        }

        // Latency Setup
        if(isLS) inst.totalCycles = EXEC_LATENCIES.LOAD;
        else if(.includes(inst.op)) inst.totalCycles = EXEC_LATENCIES.BRANCH;
        else inst.totalCycles = EXEC_LATENCIES.ALU;
        
        inst.executionCyclesLeft = inst.totalCycles;

        // 5. Update Structures
        rs.busy = true;
        rs.inst = inst;
        rs.op = inst.op;
        rs.vj = vj; rs.vk = vk;
        rs.qj = qj; rs.qk = qk;
        rs.robTag = robTag;
        
        this.rob.push({
            robTag: robTag,
            op: inst.op,
            rd: inst.rd,
            pc: inst.pc,
            instText: inst.text,
            isReady: false,
            result: 0,
            predictedTaken: false, // Default Not Taken
            targetAddr: 0
        });

        // Update RAT (Rename Destination)
        if(inst.rd!== 0 && inst.op!== 'BEQ' && inst.op!== 'BNE' && inst.op!== 'SW') {
            this.rat[inst.rd] = robTag;
        }

        // 6. Branch Prediction & PC Update
        if(inst.op === 'BEQ' |

| inst.op === 'BNE') {
            const pred = this.predictor.predict(this.pc);
            this.rob[this.rob.length-1].predictedTaken = pred;
            inst.predictedTaken = pred;
            
            if(pred) {
                this.pc += inst.imm;
                this.log(`Branch ${inst.pc} previsto TOMADO -> ${this.pc}`);
            } else {
                this.pc += 4;
            }
        } else if (inst.op === 'JAL') {
             this.pc += inst.imm;
        } else {
            this.pc += 4;
        }

        this.log(`ISSUE: ${inst.text} (ROB#${robTag})`);
        return true;
    }

    updateUI() {
        document.getElementById('metric-cycles').innerText = this.clock;
        document.getElementById('metric-pc').innerText = '0x' + this.pc.toString(16);
        document.getElementById('metric-insts').innerText = this.instructionsCommitted;
        const ipc = this.clock > 0? (this.instructionsCommitted / this.clock).toFixed(2) : "0.00";
        document.getElementById('metric-ipc').innerText = ipc;

        // Populate ROB Table
        const robBody = document.getElementById('rob-table-body');
        robBody.innerHTML = this.rob.map(r => `
            <tr class="${r.isReady? 'text-green-400' : 'text-gray-400'}">
                <td class="p-1">#${r.robTag}</td>
                <td class="p-1">${r.instText}</td>
                <td class="p-1">${r.isReady? 'DONE' : 'EXEC'}</td>
                <td class="p-1">${r.rd? 'x'+r.rd : '-'}</td>
                <td class="p-1">${r.result}</td>
            </tr>
        `).join('');

        // Populate Registers
        const regBody = document.getElementById('reg-table-body');
        regBody.innerHTML = '';
        for(let i=0; i<32; i++) {
            const ratVal = this.rat[i];
            const ratStr = ratVal === -1? '-' : `ROB#${ratVal}`;
            regBody.innerHTML += `
                <tr class="hover:bg-gray-700">
                    <td class="p-1 text-blue-300">x${i}</td>
                    <td class="p-1 register-cell">0x${this.regFile[i].toString(16).toUpperCase()}</td>
                    <td class="p-1 register-cell">${this.regFile[i]}</td>
                    <td class="p-1 text-yellow-500">${ratStr}</td>
                </tr>
            `;
        }

        // Cache Stats
        document.getElementById('l1i-access').innerText = this.l1i.accessCount;
        document.getElementById('l1i-hits').innerText = this.l1i.hitCount;
        document.getElementById('l1i-misses').innerText = this.l1i.missCount;
        document.getElementById('l1d-access').innerText = this.l1d.accessCount;
        document.getElementById('l1d-hits').innerText = this.l1d.hitCount;
        document.getElementById('l1d-misses').innerText = this.l1d.missCount;
    }
}

// Inicialização
const sim = new Simulator();

document.getElementById('btn-load').onclick = () => {
    sim.loadProgram(document.getElementById('code-input').value);
    document.getElementById('btn-step').disabled = false;
    document.getElementById('btn-run').disabled = false;
};

document.getElementById('btn-step').onclick = () => {
    sim.step();
};

let runInterval;
document.getElementById('btn-run').onclick = function() {
    if(runInterval) {
        clearInterval(runInterval);
        runInterval = null;
        this.innerText = "Run (Executar)";
        this.classList.remove('bg-red-600');
        this.classList.add('bg-purple-600');
    } else {
        runInterval = setInterval(() => {
            if(!sim.isRunning && sim.rob.length === 0 && sim.pc >= Object.keys(sim.instructions).length * 4) {
                clearInterval(runInterval);
                return;
            }
            sim.step();
        }, 100);
        this.innerText = "Stop (Parar)";
        this.classList.remove('bg-purple-600');
        this.classList.add('bg-red-600');
    }
};

document.getElementById('btn-reset').onclick = () => {
    sim.loadProgram("");
    document.getElementById('code-input').value = "";
    document.getElementById('btn-step').disabled = true;
    document.getElementById('btn-run').disabled = true;
};