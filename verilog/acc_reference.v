module acc_cpu(input clk);

// registers
reg [15:0] pc;
reg [31:0] acc;

// memories
reg [31:0] imem [0:15];
reg [31:0] dmem [0:15];

// intermediate wires
wire [31:0] instruction;
wire [31:0] read_data;
wire [1:0] op;
wire [15:0] addr;

// control signals
wire write_mem;
wire add_op;
wire branch_op;
wire write_acc;

// read mem
assign instruction = imem[pc];
assign read_data = dmem[addr];

// decode
assign op = instruction[1:0];
assign addr = instruction[31:16];

// control logic
assign write_acc = (op == 2'b00) ^ (op == 2'b01);
assign write_mem = (op == 2'b10);
assign add_op = (op == 2'b01);
assign branch_op = (op == 2'b11);
// or, equivalently:
//case (op)
//  2'b00: begin
//    assign write_acc = 1;
//    assign write_mem = 0;
//    assign add_op = 0;
//    assign branch_op = 0;
//  end
//  2'b01: begin
//    assign write_acc = 1;
//    assign write_mem = 0;
//    assign add_op = 1;
//    assign branch_op = 0;
//  end
//  2'b10: begin
//    assign write_acc = 0;
//    assign write_mem = 1;
//    assign add_op = 0;
//    assign branch_op = 0;
//  end
//  2'b11: begin
//    assign write_acc = 0;
//    assign write_mem = 0;
//    assign add_op = 0;
//    assign branch_op = 1;
//  end
//endcase

// update acc
always @(posedge clk) begin
  if (write_acc) begin
    if (add_op)
      acc <= read_data + acc;
    else
      acc <= read_data;
  end
end

// write to memory
always @(posedge clk) begin
  if (write_mem)
    dmem[addr] <= acc;
end

// update pc
always @(posedge clk) begin
  if (branch_op & (acc == 0))
    pc <= addr;
  else
    pc <= pc + 16'd1;
end

endmodule
