static void fecarry(uint32_t out[16], const uint32_t in1[16]) {
  { const uint32_t x29 = in1[15];
  { const uint32_t x30 = in1[14];
  { const uint32_t x28 = in1[13];
  { const uint32_t x26 = in1[12];
  { const uint32_t x24 = in1[11];
  { const uint32_t x22 = in1[10];
  { const uint32_t x20 = in1[9];
  { const uint32_t x18 = in1[8];
  { const uint32_t x16 = in1[7];
  { const uint32_t x14 = in1[6];
  { const uint32_t x12 = in1[5];
  { const uint32_t x10 = in1[4];
  { const uint32_t x8 = in1[3];
  { const uint32_t x6 = in1[2];
  { const uint32_t x4 = in1[1];
  { const uint32_t x2 = in1[0];
  { uint32_t x31 = (x16 >> 0x1c);
  { uint32_t x32 = (x16 & 0xfffffff);
  { uint32_t x33 = (x29 >> 0x1c);
  { uint32_t x34 = (x29 & 0xfffffff);
  { uint32_t x35 = ((0x10000000 * x33) + x34);
  { uint32_t x36 = (x35 >> 0x1c);
  { uint32_t x37 = (x35 & 0xfffffff);
  { uint32_t x38 = ((x31 + x18) + x36);
  { uint32_t x39 = (x38 >> 0x1c);
  { uint32_t x40 = (x38 & 0xfffffff);
  { uint32_t x41 = (x2 + x36);
  { uint32_t x42 = (x41 >> 0x1c);
  { uint32_t x43 = (x41 & 0xfffffff);
  { uint32_t x44 = (x39 + x20);
  { uint32_t x45 = (x44 >> 0x1c);
  { uint32_t x46 = (x44 & 0xfffffff);
  { uint32_t x47 = (x42 + x4);
  { uint32_t x48 = (x47 >> 0x1c);
  { uint32_t x49 = (x47 & 0xfffffff);
  { uint32_t x50 = (x45 + x22);
  { uint32_t x51 = (x50 >> 0x1c);
  { uint32_t x52 = (x50 & 0xfffffff);
  { uint32_t x53 = (x48 + x6);
  { uint32_t x54 = (x53 >> 0x1c);
  { uint32_t x55 = (x53 & 0xfffffff);
  { uint32_t x56 = (x51 + x24);
  { uint32_t x57 = (x56 >> 0x1c);
  { uint32_t x58 = (x56 & 0xfffffff);
  { uint32_t x59 = (x54 + x8);
  { uint32_t x60 = (x59 >> 0x1c);
  { uint32_t x61 = (x59 & 0xfffffff);
  { uint32_t x62 = (x57 + x26);
  { uint32_t x63 = (x62 >> 0x1c);
  { uint32_t x64 = (x62 & 0xfffffff);
  { uint32_t x65 = (x60 + x10);
  { uint32_t x66 = (x65 >> 0x1c);
  { uint32_t x67 = (x65 & 0xfffffff);
  { uint32_t x68 = (x63 + x28);
  { uint32_t x69 = (x68 >> 0x1c);
  { uint32_t x70 = (x68 & 0xfffffff);
  { uint32_t x71 = (x66 + x12);
  { uint32_t x72 = (x71 >> 0x1c);
  { uint32_t x73 = (x71 & 0xfffffff);
  { uint32_t x74 = (x69 + x30);
  { uint32_t x75 = (x74 >> 0x1c);
  { uint32_t x76 = (x74 & 0xfffffff);
  { uint32_t x77 = (x72 + x14);
  { uint32_t x78 = (x77 >> 0x1c);
  { uint32_t x79 = (x77 & 0xfffffff);
  { uint32_t x80 = (x75 + x37);
  { uint32_t x81 = (x80 >> 0x1c);
  { uint32_t x82 = (x80 & 0xfffffff);
  { uint32_t x83 = (x78 + x32);
  { uint32_t x84 = (x83 >> 0x1c);
  { uint32_t x85 = (x83 & 0xfffffff);
  { uint32_t x86 = ((0x10000000 * x81) + x82);
  { uint32_t x87 = (x86 >> 0x1c);
  { uint32_t x88 = (x86 & 0xfffffff);
  { uint32_t x89 = ((x84 + x40) + x87);
  { uint32_t x90 = (x89 >> 0x1c);
  { uint32_t x91 = (x89 & 0xfffffff);
  { uint32_t x92 = (x43 + x87);
  { uint32_t x93 = (x92 >> 0x1c);
  { uint32_t x94 = (x92 & 0xfffffff);
  out[0] = x94;
  out[1] = (x93 + x49);
  out[2] = x55;
  out[3] = x61;
  out[4] = x67;
  out[5] = x73;
  out[6] = x79;
  out[7] = x85;
  out[8] = x91;
  out[9] = (x90 + x46);
  out[10] = x52;
  out[11] = x58;
  out[12] = x64;
  out[13] = x70;
  out[14] = x76;
  out[15] = x88;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}