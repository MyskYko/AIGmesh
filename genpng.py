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
nLevel = int(line) + 1

ratio = 1
unit = 12

blockh = unit * 2
blockw = blockh * ratio

imgh = blockh * (4 ** nLevel)
imgw = imgh * ratio

white = (255, 255, 255)
black = (0, 0, 0)
yellow = (255, 252, 204)
blue = (173, 216, 230)

img = Image.new('RGB', (imgw, imgh), white)
draw = ImageDraw.Draw(img)
font = ImageFont.truetype('/usr/share/fonts/gnu-free/FreeMono.ttf', unit, encoding='utf-8')

def box(offx, offy, sizew, sizeh, words, color = white):
    draw.rectangle((offx, imgh - offy, offx + sizew, imgh - (offy + sizeh)), outline=black, fill = color)
    for i, word in enumerate(words):
        x = ((unit * i) // sizeh) * unit * ratio
        y = (unit * i) % sizeh
        draw.text((offx + x, imgh - (offy + y) - unit), word, font=font, fill=black)
    
def rec(level, offx, offy):
    sizeh = blockh * (4 ** level)
    sizew = sizeh * ratio
    for y in range(2):
        for x in range(2):
            offx2 = offx + 2 * sizew * x
            offy2 = offy + 2 * sizeh * y
            #V
            line = f.readline()
            words = line.split()
            box(offx2 + sizew, offy2, sizew, sizeh, words)
            #H
            line = f.readline()
            words = line.split()
            box(offx2, offy2 + sizeh, sizew, sizeh, words)
            #S
            box(offx2 + sizew, offy2 + sizeh, sizew, sizeh, [], blue)
            #P
            if level == 0:
                line = f.readline()
                words = line.split()
                box(offx2, offy2, sizew, sizeh, words, yellow)
            else:
                rec(level - 1, offx2, offy2)


rec(nLevel - 1, 0, 0)

img.save("res.png")
