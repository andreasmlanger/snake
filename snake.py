"""
Snake game trained with an evolutionary AI algorithm
"""

import neat
import tkinter as tk
from collections import deque as dq
from ctypes import c_buffer, windll
import math
import os
import pickle
import random
import time
import threading

# AI-controlled game or manual mode
AI = True

# General game parameters
SIZE = 25  # number of squares in x and y direction
CELL = 25  # width of one square in pixels
WALLS = True  # if false, then walls are transparent

# AI-related parameters
WINNER = True  # if true, only show best snake
GEN = 100  # number of generations to train

TICK_RATE = 100 if not AI else 20 if WINNER else 5
AUDIO = False if AI else True
DIRECTIONS = ['Up', 'Right', 'Down', 'Left']
DIRECTION_VECTORS = [(0, -1), (1, 0), (0, 1), (-1, 0)]


def line(x0, y0, x1, y1):
    """Bresenham's line algorithm"""
    s = set()
    dx, dy = abs(x1 - x0), abs(y1 - y0)
    x, y = x0, y0
    sx = -1 if x0 > x1 else 1
    sy = -1 if y0 > y1 else 1
    if dx > dy:
        err = dx / 2.0
        while x != x1:
            s.add((x, y))
            err -= dy
            if err < 0:
                y += sy
                err += dx
            x += sx
    else:
        err = dy / 2.0
        while y != y1:
            s.add((x, y))
            err -= dx
            if err < 0:
                x += sx
                err += dy
            y += sy
    s.add((x, y))
    return s


def create_rectangle(canvas, x, y, fill):
    """Creates snake and food squares"""
    return canvas.create_rectangle(x * CELL, y * CELL, (x + 1) * CELL, (y + 1) * CELL, fill=fill, width=0)


class Window:
    def __init__(self, parent):
        parent.title(f'SnakeAI {"(Manual Mode)" if not AI else ""}')
        parent.iconbitmap('data/snake.ico')
        parent.resizable(False, False)
        parent.geometry('+250+0')  # move window to the middle
        self.walls = WALLS
        self.audio = AUDIO
        self.paused = False
        self.colors = None
        self.restart_time = None
        self.high_score = tk.StringVar()
        self.high_score_label = tk.Label(parent, textvariable=self.high_score, width=15, height=2, font=('Verdana', 14))
        self.high_score_label.grid(row=0, column=1)
        self.score = tk.StringVar()
        self.score_label = tk.Label(parent, textvariable=self.score, width=15, height=2, font=('Verdana', 14))
        self.score_label.grid(row=1, column=1)
        self.restart_text = tk.StringVar()
        self.restart_label = tk.Label(parent, textvariable=self.restart_text, width=15, height=2, font=('Verdana', 14))
        self.restart_label.grid(row=4, column=1)
        parent.bind('w', self.toggle_wall)
        parent.bind('W', self.toggle_wall)
        parent.bind('m', self.toggle_audio)
        parent.bind('M', self.toggle_audio)

    @staticmethod
    def load_high_score():
        try:
            with open('high_score.txt', 'r') as fw:
                high_score = fw.read()
            return f'HIGH SCORE\n{high_score}'
        except (FileNotFoundError, ValueError):
            return 'HIGH SCORE\n0'

    def save_high_score(self):
        with open('high_score.txt', 'w') as fw:
            fw.write(self.high_score.get().split('\n')[1])

    @staticmethod
    def play_sound(sound, command):

        def win_command(*com):
            com = ' '.join(com).encode('utf-8')
            buf = c_buffer(255)
            windll.winmm.mciSendStringA(com, buf, 254, 0)
            return buf.value

        try:
            path = r'data/' + sound + '.mp3'
            win_command('open "' + path + '" alias', sound)
            win_command('set', sound, 'time format milliseconds')
            duration = win_command('status', sound, 'length').decode()
            if command == 'start':
                win_command('play', sound, 'from 0 to', duration)
                return int(duration) // 1000
            elif command == 'stop':
                win_command('stop', sound)
        except ValueError:
            return 0  # audio files missing

    @staticmethod
    def toggle_wall(_=None):
        window.walls = not window.walls

    def toggle_audio(self, _=None):
        window.audio = not window.audio
        if not window.audio:
            self.play_sound('music', 'stop')
        else:
            self.restart_time = time.time() + self.play_sound('music', 'start')


class Board:
    def __init__(self):
        self.canvas = tk.Canvas(root, width=SIZE * CELL + 1, height=SIZE * CELL)
        self.canvas.grid(row=0, column=0, rowspan=5)
        self.score_canvas = None
        window.colors = {'S': '#6CBB3C', 'F': '#EFD631'}  # snake & food
        self.draw_new_board()
        window.high_score.set(window.load_high_score())
        window.score.set('SCORE\n0')
        self.food_chain = self.create_food_chain()
        self.snakes = []
        self.nets = []
        self.ge = []

    def draw_new_board(self, _=None):
        self.canvas.delete(tk.ALL)
        self.canvas.create_line(SIZE * CELL + 1, 0, SIZE * CELL + 1, SIZE * CELL, width=2)  # vertical divider
        window.restart_text.set('')

    @staticmethod
    def create_food_chain():
        cells = [(x, y) for x in range(0, SIZE) for y in range(0, SIZE)]
        random.shuffle(cells)  # create random chain of food
        return cells


class Snake:
    def __init__(self, parent, board):
        self.parent = parent
        self.board = board
        self.index = len(self.board.snakes)
        for key in ('<Escape>', '<space>'):
            self.parent.bind(key, self.toggle_pause)
        self.parent.bind('n', self.restart)
        self.parent.bind('N', self.restart)
        self.parent.bind('a', self.toggle_mode)
        self.parent.bind('A', self.toggle_mode)
        self.parent.bind('<Left>', self.change_direction)
        self.parent.bind('<Right>', self.change_direction)
        self.parent.bind('<Up>', self.change_direction)
        self.parent.bind('<Down>', self.change_direction)
        self.direction = random.choice(DIRECTIONS)
        self.score = 0
        self.tick_rate = TICK_RATE
        self.ticking = None
        self.snake = None
        self.food = None
        self.health = 1
        self.direction_queue = dq()
        self.empty = [(x, y) for x in range(0, SIZE) for y in range(0, SIZE)]
        self.draw_snake()
        self.draw_food()

    def restart(self, _=None):
        self.end('')
        run()

    def toggle_mode(self, _=None):
        window.ambylopia = not window.ambylopia
        self.restart()

    def toggle_pause(self, _=None):
        window.paused = not window.paused
        if window.paused:
            if window.audio:
                window.play_sound('music', 'stop')
            self.parent.after_cancel(self.ticking)  # cancel self.tick
        else:
            if window.audio:
                window.restart_time = time.time() + window.play_sound('music', 'start')
            self.ticking = self.parent.after(self.tick_rate, self.tick)  # restart self.tick

    def draw_snake(self):
        x, y = SIZE // 2, SIZE // 2  # middle of board
        self.snake = dq([Cell(x, y, create_rectangle(self.board.canvas, x, y, fill=window.colors['S']))])
        self.ticking = self.parent.after(self.tick_rate, self.tick)
        if window.audio:
            window.restart_time = time.time() + window.play_sound('music', 'start')

    def draw_food(self):
        position = len(self.snake) - 1
        while True:  # find a free spot on the board
            if self.board.food_chain[position] in self.empty:
                x, y = self.board.food_chain[position]
                break
            position += 1
            if position == len(self.board.food_chain):
                position = 0
        self.food = Cell(x, y, create_rectangle(self.board.canvas, x, y, fill=window.colors['F']))

    def change_direction(self, event=None):
        x, y = self.snake[0].x, self.snake[0].y  # snake head

        # Obstacles
        snake = set([(self.snake[i].x, self.snake[i].y) for i in range(1, len(self.snake))])  # everything but the head
        walls = set([(-1, i - 1) for i in range(SIZE + 2)] + [(SIZE, i - 1) for i in range(SIZE + 2)] +
                    [(i - 1, -1) for i in range(SIZE + 2)] + [(i - 1, SIZE) for i in range(SIZE + 2)])
        no_go = snake.union(walls)

        # Fields in all 8 directions from snake head
        uu = [(x, y - 1 - i) for i in range(y + 1)]  # up
        ur = [(x + 1 + i, y - 1 - i) for i in range(min(SIZE - x, y + 1))]
        rr = [(x + 1 + i, y) for i in range(SIZE - x)]  # right
        rd = [(x + 1 + i, y + 1 + i) for i in range(min(SIZE - x, SIZE - y))]
        dd = [(x, y + 1 + i) for i in range(SIZE - y)]  # down
        dl = [(x - 1 - i, y + 1 + i) for i in range(min(x + 1, SIZE - y))]
        ll = [(x - 1 - i, y) for i in range(x + 1)]  # left
        lu = [(x - 1 - i, y - 1 - i) for i in range(min(x + 1, y + 1))]

        if self.direction == 'Up':
            choices = [dl, ll, lu, uu, ur, rr, rd]
        elif self.direction == 'Right':
            choices = [lu, uu, ur, rr, rd, dd, dl]
        elif self.direction == 'Down':
            choices = [ur, rr, rd, dd, dl, ll, lu]
        else:  # left
            choices = [rd, dd, dl, ll, lu, uu, ur]

        obstacles = []
        for choice in choices:
            for idx, tup in enumerate(choice):
                if tup in no_go:
                    if idx == 0:
                        obstacles.append(-1)
                    elif idx == 1:
                        obstacles.append(-0.5)
                    elif idx == 2:
                        obstacles.append(0)
                    elif idx == 3:
                        obstacles.append(0.5)
                    else:
                        obstacles.append(1)
                    break

        # Angles towards food and tail
        food_x, food_y = tuple(self.food)
        angle = math.atan2(food_y - y, food_x - x)

        if self.direction == 'Left':
            angle -= math.pi
        elif self.direction == 'Down':
            angle -= math.pi / 2
        elif self.direction == 'Up':
            angle += math.pi / 2

        if angle > math.pi:
            angle -= 2 * math.pi
        elif angle < -math.pi:
            angle += 2 * math.pi

        # If snake is in between the head and food, make food invisible
        if line(x, y, food_x, food_y) & snake:
            angle = 0

        if AI:
            unit = 1 / SIZE ** 2 * max(1, 10 - len(self.snake))  # short snakes starve sooner
            self.health -= unit  # lose health with every tick
            if self.health < 0:  # eliminate infinite loop snakes
                self.end('')

            inputs = obstacles + [angle]
            output = self.board.nets[self.index].activate(inputs)

            if output[0] == max(output):  # turn left
                self.direction = DIRECTIONS[(DIRECTIONS.index(self.direction) - 1) % 4]
            elif output[2] == max(output):  # turn right
                self.direction = DIRECTIONS[(DIRECTIONS.index(self.direction) + 1) % 4]

        elif event:
            if len(self.direction_queue) == 0:
                if {event.keysym, self.direction} not in ({'Left', 'Right'}, {'Up', 'Down'}) and \
                        event.keysym != self.direction:
                    self.direction_queue.appendleft(event.keysym)  # prevent turning around
            else:
                if {event.keysym, self.direction_queue[0]} not in ({'Left', 'Right'}, {'Up', 'Down'}) and \
                        event.keysym != self.direction_queue[0]:
                    self.direction_queue.appendleft(event.keysym)

    def tick(self):
        self.ticking = self.parent.after(self.tick_rate, self.tick)
        self.move()

    def move(self):
        self.change_direction()
        if self.direction_queue:
            self.direction = self.direction_queue.pop()

        head = self.snake[0]
        tail = self.snake[-1]
        x, y = head

        if self.direction == 'Left':
            target = x - 1, y
        elif self.direction == 'Right':
            target = x + 1, y
        elif self.direction == 'Up':
            target = x, y - 1
        else:  # down
            target = x, y + 1

        if not window.walls:  # transparent walls
            if target[0] == - 1:
                target = SIZE - 1, y
            elif target[0] == SIZE:
                target = 0, y
            elif target[1] == - 1:
                target = x, SIZE - 1
            elif target[1] == SIZE:
                target = x, 0

        if target == (self.food.x, self.food.y):  # eating
            self.board.canvas.itemconfig(self.food.square, fill=window.colors['S'], width=0)  # recolor food
            self.snake.appendleft(self.food)
            self.score += 1
            if self.score > int(window.score.get().split('\n')[1]):
                window.score.set(f'SCORE\n{self.score}')
            if self.score > int(window.load_high_score().split('\n')[1]):
                window.high_score.set(f'HIGH SCORE\n{self.score}')
                window.save_high_score()
            if window.audio:
                thread = threading.Thread(target=window.play_sound, args=('eat', 'start'))
                thread.start()
            self.draw_food()
            self.health = 1  # reset snake health
            if AI:
                self.board.ge[self.index].fitness += 1  # reward snakes that find food
            return

        if target not in self.empty and target != (tail.x, tail.y):  # collision
            self.end('') if AI else self.end(f'GAME OVER')
            return

        self.empty.append((tail.x, tail.y))
        self.empty.remove(target)
        tail.x, tail.y = target
        self.board.canvas.coords(self.snake[-1].square, *(a * CELL for a in target), *((a + 1) * CELL for a in target))
        self.snake.appendleft(self.snake.pop())

        if window.audio and time.time() > window.restart_time:
            window.restart_time = time.time() + window.play_sound('music', 'start')

    def end(self, text):
        self.parent.after_cancel(self.ticking)
        if window.audio and text != '':
            window.play_sound('music', 'stop')
            window.play_sound('lose', 'start')
        if AI:
            self.board.snakes[self.index] = 0
            self.board.canvas.delete(self.food.square)
            for idx in range(len(self.snake)):
                self.board.canvas.delete(self.snake[idx].square)
        else:
            self.board.canvas.create_text(SIZE * CELL // 2, SIZE * CELL // 2, text=text,
                                          font=('Verdana', SIZE * CELL // 10), fill='black')
            window.restart_text.set("PRESS 'N'\nTO RESTART")


class Cell:
    def __init__(self, x, y, square):
        self.x = x
        self.y = y
        self.square = square

    def __iter__(self):
        yield self.x
        yield self.y


def evolve(genomes=None, conf=None):
    print('High score: ' + '\033[92m' + window.load_high_score().split('\n')[1] + '\033[0m')
    board = Board()
    if not AI:
        Snake(root, board)
        root.mainloop()
    else:
        for _, g in genomes:
            net = neat.nn.FeedForwardNetwork.create(g, conf)
            board.nets.append(net)
            board.snakes.append(Snake(root, board))
            g.fitness = 0
            board.ge.append(g)

        while any([x for x in board.snakes]):
            root.update_idletasks()
            root.update()
        for idx in range(len(board.snakes) - 1, -1, -1):
            del board.snakes[idx]
        for idx in range(len(board.nets) - 1, -1, -1):
            del board.nets[idx]
        for idx in range(len(board.ge) - 1, -1, -1):
            del board.ge[idx]


def run():
    if not AI:
        evolve()
    else:
        config = neat.config.Config(neat.DefaultGenome, neat.DefaultReproduction, neat.DefaultSpeciesSet,
                                    neat.DefaultStagnation, 'data/config.txt')

        if WINNER and os.path.isfile('best_snake.pickle'):
            with open(f'best_snake.pickle', 'rb') as f:
                winner = pickle.load(f)
                evolve([(None, winner)], config)
        else:
            if os.path.isfile('population.pickle'):
                with open(f'population.pickle', 'rb') as f:
                    p = pickle.load(f)
            else:
                p = neat.Population(config)
                # p = neat.Checkpointer.restore_checkpoint('neat-checkpoint-1')  # uncomment to continue from checkpoint

                p.add_reporter(neat.StdOutReporter(True))
                stats = neat.StatisticsReporter()
                p.add_reporter(stats)
                # p.add_reporter(neat.Checkpointer(1))  # uncomment to add checkpoints

            winner = p.run(evolve, GEN)  # run for up to GEN generations
            print('\nBest genome:\n{!s}'.format(winner))  # show final stats
            with open('population.pickle', 'wb') as f:
                pickle.dump(p, f)
            with open('best_snake.pickle', 'wb') as f:
                pickle.dump(winner, f)


if __name__ == '__main__':
    root = tk.Tk()
    window = Window(root)
    run()
