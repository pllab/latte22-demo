module acc_holes(input clk);

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
(* hole_width=1, hole_params="op" *) wire write_mem;
(* hole_width=1, hole_params="op" *) wire add_op;
(* hole_width=1, hole_params="op" *) wire branch_op;
(* hole_width=1, hole_params="op" *) wire write_acc;

// read mem
assign instruction = imem[pc];
assign read_data = dmem[addr];

// decode
assign op = instruction[1:0];
assign addr = instruction[31:16];

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
