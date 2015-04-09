# Point-and-shoot camera for Raspberry Pi w/camera and Adafruit PiTFT.
# This must run as root (sudo python cam.py) due to framebuffer, etc.
#
# Adafruit invests time and resources providing this open source code, 
# please support Adafruit and open-source development by purchasing 
# products from Adafruit, thanks!
#
# http://www.adafruit.com/products/998  (Raspberry Pi Model B)
# http://www.adafruit.com/products/1367 (Raspberry Pi Camera Board)
# http://www.adafruit.com/products/1601 (PiTFT Mini Kit)
# This can also work with the Model A board and/or the Pi NoIR camera.
#
# Prerequisite tutorials: aside from the basic Raspbian setup and
# enabling the camera in raspi-config, you should configure WiFi (if
# using wireless with the Dropbox upload feature) and read these:
# PiTFT setup (the tactile switch buttons are not required for this
# project, but can be installed if you want them for other things):
# http://learn.adafruit.com/adafruit-pitft-28-inch-resistive-touchscreen-display-raspberry-pi
# Dropbox setup (if using the Dropbox upload feature):
# http://raspi.tv/2013/how-to-use-dropbox-with-raspberry-pi
#
# Written by Phil Burgess / Paint Your Dragon for Adafruit Industries.
# BSD license, all text above must be included in any redistribution.

import atexit
import cPickle as pickle
import errno
import fnmatch
import io
import os
import os.path
import picamera
import pygame
import stat
import threading
import time
import yuv2rgb
from pygame.locals import *
from subprocess import call  
import argparse
import uuid

parser = argparse.ArgumentParser()
parser.add_argument("-s","--storagepath", help="set the storage path", type=str)
args = parser.parse_args()

# UI classes ---------------------------------------------------------------

# Small resistive touchscreen is best suited to simple tap interactions.
# Importing a big widget library seemed a bit overkill.  Instead, a couple
# of rudimentary classes are sufficient for the UI elements:

# Icon is a very simple bitmap class, just associates a name and a pygame
# image (PNG loaded from icons directory) for each.
# There isn't a globally-declared fixed list of Icons.  Instead, the list
# is populated at runtime from the contents of the 'icons' directory.

class Icon:

	def __init__(self, name):
	  self.name = name
	  try:
	    self.bitmap = pygame.image.load(iconPath + '/' + name + '.png')
	  except:
	    pass

# Button is a simple tappable screen region.  Each has:
#  - bounding rect ((X,Y,W,H) in pixels)
#  - optional background color and/or Icon (or None), always centered
#  - optional foreground Icon, always centered
#  - optional text, always centered
#  - optional single callback function
#  - optional single value passed to callback
# Occasionally Buttons are used as a convenience for positioning Icons
# but the taps are ignored.  Stacking order is important; when Buttons
# overlap, lowest/first Button in list takes precedence when processing
# input, and highest/last Button is drawn atop prior Button(s).  This is
# used, for example, to center an Icon by creating a passive Button the
# width of the full screen, but with other buttons left or right that
# may take input precedence (e.g. the Effect labels & buttons).
# After Icons are loaded at runtime, a pass is made through the global
# buttons[] list to assign the Icon objects (from names) to each Button.

class Button:

	def __init__(self, rect, **kwargs):
	  self.rect       = rect # Bounds
	  self.color      = None # Background fill color, if any
	  self.iconBg     = None # Background Icon (atop color fill)
	  self.iconFg     = None # Foreground Icon (atop background)
	  self.bg         = None # Background Icon name
	  self.fg         = None # Foreground Icon name
	  self.callback   = None # Callback function
	  self.value      = None # Value passed to callback
	  self.text       = None
	  self.renderText = None
	  self.fontSize   = None
	  for key, value in kwargs.iteritems():
	    if   key == 'color': self.color    = value
	    elif key == 'bg'   : self.bg       = value
	    elif key == 'fg'   : self.fg       = value
	    elif key == 'cb'   : self.callback = value
	    elif key == 'value': self.value    = value
	    elif key == 'text' : self.text     = value
	    elif key == 'fontSize' : self.fontSize     = value
	  if self.text:
	    if self.fontSize is not None:
	      font = pygame.font.SysFont("Arial",self.fontSize)
	    else:
	      font = pygame.font.SysFont("Arial",60)

	    self.renderText=font.render(self.text, True, (255,255,255))
	def selected(self, pos):
	  x1 = self.rect[0]
	  y1 = self.rect[1]
	  x2 = x1 + self.rect[2] - 1
	  y2 = y1 + self.rect[3] - 1
	  if ((pos[0] >= x1) and (pos[0] <= x2) and
	      (pos[1] >= y1) and (pos[1] <= y2)):
	    if self.callback:
	      if self.value is None: self.callback()
	      else:                  self.callback(self.value)
	    return True
	  return False

	def draw(self, screen):
	  if self.color:
	    screen.fill(self.color, self.rect)
	  if self.iconBg:
	    screen.blit(self.iconBg.bitmap,
	      (self.rect[0]+(self.rect[2]-self.iconBg.bitmap.get_width())/2,
	       self.rect[1]+(self.rect[3]-self.iconBg.bitmap.get_height())/2))
	  if self.iconFg:
	    screen.blit(self.iconFg.bitmap,
	      (self.rect[0]+(self.rect[2]-self.iconFg.bitmap.get_width())/2,
	       self.rect[1]+(self.rect[3]-self.iconFg.bitmap.get_height())/2))
	  if self.text:
	    screen.blit(self.renderText,
                    (self.rect[0]+(self.rect[2]-self.renderText.get_width())/2,
                     self.rect[1]+(self.rect[3]-self.renderText.get_height())/2))


	def setBg(self, name):
	  if name is None:
	    self.iconBg = None
	  else:
	    for i in icons:
	      if name == i.name:
	        self.iconBg = i
	        break


def fxCallback(n): # Pass 1 (next effect) or -1 (prev effect)
	global fxMode
	setFxMode((fxMode + n) % len(fxData))

def printCallBack():
	global screenMode
	screenMode=0

def backToNormal():
	global screenMode
	screenMode=0

# Global stuff -------------------------------------------------------------
screenMode = 0
fxMode          =  0      # Image effect; default = Normal
scaled          = None    # pygame Surface w/last-loaded image
sizeData = [(2592, 1944), (320, 240), (0.0   , 0.0   , 1.0   , 1.0   )] # Large
storagePath=args.storagepath+"/"
filePath = storagePath+str(uuid.uuid4())+"_"
photoCount = 0
lastImage = None
iconPath        = 'icons' # Subdirectory containing UI bitmaps (PNG format)

print "Will store photos to ", storagePath
# A fixed list of image effects is used (rather than polling
# camera.IMAGE_EFFECTS) because the latter contains a few elements
# that aren't valid (at least in video_port mode) -- e.g. blackboard,
# whiteboard, posterize (but posterise, British spelling, is OK).
# Others have no visible effect (or might require setting add'l
# camera parameters for which there's no GUI yet) -- e.g. saturation,
# colorbalance, colorpoint.
fxData = [
  'none', 'blackWhite','sketch', 'pastel',
  'negative','emboss', 'cartoon', 'solarize' ]


# Assorted utility functions -----------------------------------------------
def setFxMode(n):
	global fxMode,screenModes,fxLabels
	fxMode = n
	if fxData[fxMode] is not 'blackWhite':
	  camera.color_effects=None
	  camera.image_effect = fxData[fxMode]
	else:
	  camera.color_effects=(128,128)

	screenModes[0][0] = fxLabels[n]

workingLabel=Button(( 88, 51,157,102))  # 'Working' label (when enabled)
workingSpinner=Button((148, 110,22, 22))

# Busy indicator.  To use, run in separate thread, set global 'busy'
# to False when done.
def spinner():
	global busy

	workingLabel.setBg('working')
	workingLabel.draw(screen)
	pygame.display.update()

	busy = True
	n    = 0
	while busy is True:
	  workingSpinner.setBg('work-' + str(n))
	  workingSpinner.draw(screen)
	  pygame.display.update()
	  n = (n + 1) % 5
	  time.sleep(0.15)

	workingLabel.setBg(None)
	workingSpinner.setBg(None)


# Initialization -----------------------------------------------------------

# Init framebuffer/touchscreen environment variables
os.putenv('SDL_VIDEODRIVER', 'fbcon')
os.putenv('SDL_FBDEV'      , '/dev/fb1')
os.putenv('SDL_MOUSEDRV'   , 'TSLIB')
os.putenv('SDL_MOUSEDEV'   , '/dev/input/touchscreen')

# Buffers for viewfinder data
rgb = bytearray(320 * 240 * 3)
yuv = bytearray(320 * 240 * 3 / 2)

# Init pygame and screen
pygame.init()
pygame.mouse.set_visible(False)
screen = pygame.display.set_mode((0,0), pygame.FULLSCREEN)

fxLabels = [Button(( 122, 0,75,30),text="Pas d'effet",fontSize=20),
            Button(( 122, 0,75,30),text="Noir et blanc",fontSize=20),
            Button(( 122, 0,75,30),text="Croquis",fontSize=20),
            Button(( 122, 0,75,30),text="Pastel",fontSize=20),
            Button(( 122, 0,75,30),text="Negatif",fontSize=20),
            Button(( 122, 0,75,30),text="Emboss",fontSize=20),
            Button(( 122, 0,75,30),text="Cartoon",fontSize=20),
            Button(( 122, 0,75,30),text="Solaire",fontSize=20)
]

timerDisplays = [Button(( 88, 51,157,102),text="5"),
                 Button(( 88, 51,157,102),text="4"),
                 Button(( 88, 51,157,102),text="3"),
                 Button(( 88, 51,157,102),text="2"),
                 Button(( 88, 51,157,102),text="1")]

timerToDisplay = None

def fiveSecs():
    global timerToDisplay,timerDisplays

    for b in timerDisplays:
        timerToDisplay=b
        time.sleep(1)

    timerToDisplay=None

# Init camera and set up default values
camera            = picamera.PiCamera()
atexit.register(camera.close)
camera.resolution = sizeData[1]
#camera.crop       = sizeData[sizeMode][2]
camera.crop       = (0.0, 0.0, 1.0, 1.0)
# Leave raw format at default YUV, don't touch, don't set to RGB!

icons = []
# Load all icons at startup.
for file in os.listdir(iconPath):
  if fnmatch.fnmatch(file, '*.png'):
    icons.append(Icon(file.split('.')[0]))

screenModes = [
    # Screen mode 0 is effect choosing and taking photos
    [fxLabels[0],
     Button((  0, 70, 80, 52), bg='prev', cb=fxCallback     , value=-1),
             Button((240, 70, 80, 52), bg='next', cb=fxCallback     , value= 1)],
    # Screen mode 1 is print or not
    [   Button(( 122, 0,75,50),text="Imprimer ?",fontSize=40),
        Button((  0, 70, 80, 52), text='oui', fontSize=40, cb=printCallBack),
        Button((240, 70, 80, 52), text='non', fontSize=40, cb=backToNormal)]
    ]

for s in screenModes:
    for b in s:
        for i in icons:
            if b.bg== i.name:
                b.iconBg=i
                b.bg = None
            if b.fg == i.name:
                b.iconFg = i
                b.fg= None
# Main loop ----------------------------------------------------------------
def showLastImage():
    global lastImage
    screen.blit(lastImage,
                ((320 - lastImage.get_width() ) / 2,
                 (240 - lastImage.get_height()) / 2))

def takeMyPicture():
    global busy, Scaled, filePath, photoCount, screenMode, lastImage

    # If no buttons are selected we should really take the picture..
    scaled = None
    camera.resolution = sizeData[0]
    camera.crop       = sizeData[2]
    t = threading.Thread(target=spinner)
    t.start()
    camera.capture(filePath+str(photoCount)+".jpeg", use_video_port=False, format='jpeg',
                   thumbnail=None)
    busy=False
    img = pygame.image.load(filePath+str(photoCount)+".jpeg")
    lastImage = pygame.transform.scale(img, sizeData[1])
    t.join()
    camera.resolution = sizeData[1]
    camera.crop       = (0.0, 0.0, 1.0, 1.0)
    photoCount+=1
    screenMode=1

def displayCameraOnScreen():
    stream = io.BytesIO() # Capture into in-memory stream
    camera.capture(stream, use_video_port=True, format='raw')
    stream.seek(0)
    stream.readinto(yuv)  # stream -> YUV buffer
    stream.close()
    yuv2rgb.convert(yuv, rgb, sizeData[1][0],
                sizeData[1][1])
    img = pygame.image.frombuffer(rgb[0:
    (sizeData[1][0] * sizeData[1][1] * 3)],
                              sizeData[1], 'RGB')

    if img is None or img.get_height() < 240: # Letterbox, clear background
        screen.fill(0)
    if img:
        screen.blit(img,
                ((320 - img.get_width() ) / 2,
                 (240 - img.get_height()) / 2))
awaitsForPicture=False

while(True):

  for event in pygame.event.get():
    if(event.type is MOUSEBUTTONDOWN):
      pos = pygame.mouse.get_pos()
      selected=False
      for b in screenModes[screenMode]:
        if b.selected(pos):
          selected=True
          break

        # If we haven't clicked on a button and "just on the screen"
      if not selected:
        awaitsForPicture=True
        t = threading.Thread(target=fiveSecs)
        t.start()

  if screenMode is 0:
    displayCameraOnScreen()
  else:
    showLastImage()

  # Overlay buttons on display and update
  for i,b in enumerate(screenModes[screenMode]):
    b.draw(screen)

  if timerToDisplay is not None:
      timerToDisplay.draw(screen)


  if timerToDisplay is None and awaitsForPicture is True:
      awaitsForPicture=False
      takeMyPicture()

  pygame.display.update()
