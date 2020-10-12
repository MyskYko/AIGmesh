import sys
import math
import itertools
import time
import os
from PIL import Image, ImageDraw, ImageFont

try:
    f = open(sys.argv[1], "r")
except:
    exit()

line = f.readline()
nLevel = int(line.split()[0]) + 1
nObjs = int(line.split()[1])

digit = 0
while nObjs != 0:
    digit += 1
    nObjs = nObjs // 10

ratio = digit // 2 + 1
unit = 12

imgh = 8
for i in range(nLevel - 1):
    imgh = 2 * (imgh + 2 ** (i + 1))
print(imgh)
imgh = imgh * unit
imgw = imgh * ratio

white = (255, 255, 255)
black = (0, 0, 0)
yellow = (255, 252, 204)
blue = (173, 216, 230)

img = Image.new('RGB', (imgw, imgh), white)
draw = ImageDraw.Draw(img)
font = ImageFont.truetype('/usr/share/fonts/gnu-free/FreeMono.ttf', unit, encoding='utf-8')

def box(offx, offy, width, height, words, color = white):
    draw.rectangle((offx, imgh - offy, offx + width, imgh - (offy + height)), outline=black, fill = color)
    for i, word in enumerate(words):
        x = ((unit * i) // height) * unit * ratio
        y = (unit * i) % height
        draw.text((offx + x, imgh - (offy + y) - unit), word, font=font, fill=black)
    
def rec(level, offx, offy, height):
    height2 = height // 2
    width2 = height2 * ratio
    for y in range(2):
        for x in range(2):
            offx2 = offx + width2 * x
            offy2 = offy + height2 * y
            if level == 0:
                shortl = height2 // 2
            else:
                shortl = unit * (2 ** level)
            longl = height2 - shortl
            #V
            line = f.readline()
            words = line.split()
            box(offx2 + longl * ratio, offy2, shortl * ratio, longl, words)
            #H
            line = f.readline()
            words = line.split()
            box(offx2, offy2 + longl, longl * ratio, shortl, words)
            #S
            box(offx2 + longl * ratio, offy2 + longl, shortl * ratio, shortl, [], blue)
            if level == 0:
                #P
                line = f.readline()
                words = line.split()
                box(offx2, offy2, longl, longl, words, yellow)
            else:
                #P
                rec(level - 1, offx2, offy2, longl)


rec(nLevel - 1, 0, 0, imgh)

img.save("res.png")
