package states;

import org.newdawn.slick.Color;

import basic.Board;
import basic.Keys;
import basic.State;
import basic.Util;

public class MenuState implements State {
	
	private Board b;

	public MenuState(Board b) {	
		this.b = b;
		b.getSounds().fadeMusic("Menu");
	}

	private int timer = 0;
	private int selected = 0;
	private int selectCD = 0;
	private boolean startGame = false;
	
	@Override
	public void Tick() {
		String toWrite = "See the world";
		if (timer >= 600) { b.setState(new GameState(b)); return; }
		if (!startGame) { timer = timer == 300 ? 300 : timer + 1; }
		else { timer++; toWrite = "You in for a treat!";}
		Util.write(toWrite, 30, b.getWidth()/2, timer/2, fadeIn(timer), b.getTex());
		Util.drawTexture(64, 128, timer*b.getWidth()/(300*2), b.getHeight()/2, b.getTex().getTexture(animWarlock(timer)), fadeIn(timer));
		if (timer == 300) {
				selectCD = selectCD <= 0 ? 0 : selectCD - 1;
				Keys k = b.getKeys();
			if (selectCD <= 0 && (k.isDown("W") || k.isDown("S"))) {
				selected = 1 - selected;
				selectCD = 10;
			}
			if (selected == 0) {
				Util.drawSquare(20, 20, b.getWidth()/3f, b.getHeight()/1.5f, Color.red);
				if (k.isDown("Enter") || k.isDown("Space")) {
					startGame = true;
				}
			}
			else {
				Util.drawSquare(20, 20, b.getWidth()/3f, b.getHeight()/1.3f, Color.blue);
			}
			Util.write("New game", 20, b.getWidth()/2, b.getHeight()/1.5f, Color.white, b.getTex());
			Util.write(selected == 0 ? "Continue" : "Not done", 20, b.getWidth()/2, b.getHeight()/1.3f, Color.white, b.getTex());
		}
	}
	
	private Color trans(float x) {
		return new Color(x, x, x);
	}
	
	private Color fadeIn(float timer) {
		if (timer == 300) return trans(1);
		return trans(timer <= 300 ? timer/300 : (600-timer)/300); 
	}
	
	private String animWarlock(int timer) {
		if (timer == 300) { return "Warlock/Down1"; }
		else if (timer % 32 <= 8 || (timer % 32 >= 16 && timer % 32 <= 24)) return "Warlock/Right1";
		else if (timer % 32 <= 16) return "Warlock/Right2";
		return "Warlock/Right3";
	}

	@Override
	public float getCamX() {
		return 0;
	}

	@Override
	public float getCamY() {
		return 0;
	}

}
