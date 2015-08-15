package basic;

import paulscode.sound.SoundSystem;
import paulscode.sound.SoundSystemConfig;
import paulscode.sound.codecs.CodecJOrbis;
import paulscode.sound.libraries.LibraryLWJGLOpenAL;

public class Sounds {
	
	private SoundSystem ss;
	private float vol = 0;

	public Sounds() {
		try {
			SoundSystemConfig.addLibrary( LibraryLWJGLOpenAL.class ); 
			SoundSystemConfig.setCodec( "ogg", CodecJOrbis.class );
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		
		ss = new SoundSystem();
		ss.backgroundMusic("MUSIC", "Silence.ogg", true);
		
	}
	
	public void setVolume(float vol) {
		ss.setVolume("MUSIC", vol);
	}
	
	public void playMusic(String name) {
		ss.backgroundMusic("MUSIC", name+".ogg", true);
	}
	
	public void playSound(String name) {
		ss.quickPlay(false, name+".ogg", false, 0, 0, 0, SoundSystemConfig.ATTENUATION_NONE, 0);
	}
	
	public void fadeMusic(String name) {
		ss.fadeOutIn("MUSIC", name+".ogg", 1000, 5000);
	}
}
