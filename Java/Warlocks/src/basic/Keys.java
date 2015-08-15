package basic;

import java.util.HashMap;

import org.lwjgl.input.Keyboard;

public class Keys {
	private HashMap<String, Boolean> keys;

	public Keys() {
		keys = new HashMap<String, Boolean>();
		keys.put("W", false);
		keys.put("D", false);
		keys.put("A", false);
		keys.put("S", false);
		keys.put("K", false);
		keys.put("Enter", false);
		keys.put("Space", false);
	}
	
	public boolean isDown(String key) {
		return keys.get(key);
	}

	public void pollInput() {
		while (Keyboard.next()) {
			if (Keyboard.getEventKeyState()) {
				if (Keyboard.getEventKey() == Keyboard.KEY_W) {
					keys.put("W", true);
				}	
				if (Keyboard.getEventKey() == Keyboard.KEY_A) {
					keys.put("A", true);
				}	
				if (Keyboard.getEventKey() == Keyboard.KEY_S) {
					keys.put("S", true);
				}
				if (Keyboard.getEventKey() == Keyboard.KEY_D) {
					keys.put("D", true);
				}
				if (Keyboard.getEventKey() == Keyboard.KEY_K) {
					keys.put("K", true);
				}
				if (Keyboard.getEventKey() == Keyboard.KEY_RETURN) {
					keys.put("Enter", true);
				}
				if (Keyboard.getEventKey() == Keyboard.KEY_SPACE) {
					keys.put("Space", true);
				}
			} else {
				if (Keyboard.getEventKey() == Keyboard.KEY_W) {
					keys.put("W", false);
				}
				if (Keyboard.getEventKey() == Keyboard.KEY_A) {
					keys.put("A", false);
				}
				if (Keyboard.getEventKey() == Keyboard.KEY_S) {
					keys.put("S", false);
				}
				if (Keyboard.getEventKey() == Keyboard.KEY_D) {
					keys.put("D", false);
				}
				if (Keyboard.getEventKey() == Keyboard.KEY_K) {
					keys.put("K", false);
				}
				if (Keyboard.getEventKey() == Keyboard.KEY_RETURN) {
					keys.put("Enter", false);
				}
				if (Keyboard.getEventKey() == Keyboard.KEY_SPACE) {
					keys.put("Space", false);
				}
			}
		}
	}
}

